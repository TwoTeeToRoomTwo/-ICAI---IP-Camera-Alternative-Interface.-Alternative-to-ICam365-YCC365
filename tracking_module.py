# tracking_module.py
import threading
import numpy as np
import cv2
import os
import time
import traceback
from collections import deque

try:
    from ultralytics import YOLO

    YOLO_AVAILABLE = True
except Exception:
    YOLO_AVAILABLE = False


class CameraTracker:
    def __init__(self, app):
        self.app = app
        self.tracking_active = False
        self.frame_queue = deque(maxlen=2)
        self.yolo_model = None
        self.use_yolo = False
        self.confidence_threshold = 0.5
        self.last_frame = None
        self.background_subtractor = cv2.createBackgroundSubtractorMOG2(
            history=400, varThreshold=60, detectShadows=True
        )
        self.motion_threshold = 600
        self.detected_objects = []  # Списък за съхранение на откритите обекти
        self.smoothed_objects = {}  # За плавно проследяване
        self.object_id_counter = 0
        self.person_detected_flags = {}  # Флагове за открити хора по камери
        self.last_person_detection_time = {}  # Време на последното откриване

    def _load_yolo(self):
        if not YOLO_AVAILABLE:
            print("[Tracking] Ultralytics YOLOv12 липсва, motion fallback активен.")
            return
        try:
            model_path = os.path.join(os.path.dirname(__file__), "YOLOv12/yolov12n.pt")
            if not os.path.exists(model_path):
                print(f"[Tracking] YOLOv12 моделът липсва: {model_path}")
                return
            self.yolo_model = YOLO(model_path)
            self.use_yolo = True
            print(f"[Tracking] YOLOv12 зареден успешно: {model_path}")
        except Exception as e:
            print(f"[Tracking] Грешка при зареждане на YOLO: {e}")
            traceback.print_exc()

    def unload_yolo(self):
        """Разтоварва модела при спиране, за освобождаване на RAM."""
        self.yolo_model = None
        self.use_yolo = False
        print("[Tracking] YOLOv12 моделът е разтоварен.")

    def set_confidence(self, value):
        try:
            self.confidence_threshold = float(value)
            self.app.set_status(f"Чувствителност: {self.confidence_threshold:.2f}")
        except Exception:
            pass

    def start_tracking(self):
        if self.tracking_active:
            return
        self._load_yolo()  # Зареждаме само при старт
        self.tracking_active = True
        self.stop_tracking_flag = False
        self.smoothed_objects = {}  # Изчистваме плаващите обекти
        self.tracking_thread = threading.Thread(target=self._tracking_loop, daemon=True)
        self.tracking_thread.start()
        self.app.set_status("Разпознаване: ВКЛ")

        # Запазваме състоянието в конфигурацията
        current_cam = self.app.get_current_camera()
        if current_cam:
            current_cam["tracking_enabled"] = True
            self.app.save_config()

    def stop_tracking(self):
        if not self.tracking_active:
            return
        self.stop_tracking_flag = True
        self.tracking_active = False
        self.unload_yolo()
        self.detected_objects = []  # Изчистваме списъка с открити обекти
        self.smoothed_objects = {}  # Изчистваме плаващите обекти
        self.app.set_status("Разпознаване: ИЗКЛ")

        # Запазваме състоянието в конфигурацията
        current_cam = self.app.get_current_camera()
        if current_cam:
            current_cam["tracking_enabled"] = False
            self.app.save_config()

    def update_frame(self, frame):
        if frame is None:
            return
        if len(self.frame_queue) < self.frame_queue.maxlen:
            self.frame_queue.append(frame.copy())
        else:
            self.frame_queue.popleft()
            self.frame_queue.append(frame.copy())

    def _tracking_loop(self):
        while self.tracking_active and not getattr(self, "stop_tracking_flag", False):
            if not self.frame_queue:
                time.sleep(0.03)  # Намалено изчакване
                continue
            try:
                frame = self.frame_queue[-1]
                self.draw_detections(frame)
                time.sleep(0.03)  # Намалено изчакване за по-плавно движение
            except Exception as e:
                print(f"[Tracking] Loop error: {e}")
                time.sleep(0.1)

    def _smooth_coordinates(self, current_objects):
        """Плавно проследяване на обектите"""
        smoothed = []

        for i, (x1, y1, x2, y2, conf, label) in enumerate(current_objects):
            # Създаваме уникален идентификатор за обекта
            obj_key = f"{label}_{x1}_{y1}"

            if obj_key in self.smoothed_objects:
                # Плавно придвижване към новите координати
                alpha = 0.1  # По-ниска стойност за още по-плавно движение
                prev_x1, prev_y1, prev_x2, prev_y2, prev_conf, prev_label = (
                    self.smoothed_objects[obj_key]
                )

                smooth_x1 = int(prev_x1 * (1 - alpha) + x1 * alpha)
                smooth_y1 = int(prev_y1 * (1 - alpha) + y1 * alpha)
                smooth_x2 = int(prev_x2 * (1 - alpha) + x2 * alpha)
                smooth_y2 = int(prev_y2 * (1 - alpha) + y2 * alpha)
                smooth_conf = prev_conf * (1 - alpha) + conf * alpha

                smoothed_obj = (
                    smooth_x1,
                    smooth_y1,
                    smooth_x2,
                    smooth_y2,
                    smooth_conf,
                    label,
                )
                self.smoothed_objects[obj_key] = smoothed_obj
                smoothed.append(smoothed_obj)
            else:
                # Ново разпознаване
                self.smoothed_objects[obj_key] = (x1, y1, x2, y2, conf, label)
                smoothed.append((x1, y1, x2, y2, conf, label))

        # Премахваме старите обекти, които не са видими
        current_keys = {
            f"{label}_{x1}_{y1}" for x1, y1, x2, y2, conf, label in current_objects
        }
        self.smoothed_objects = {
            k: v for k, v in self.smoothed_objects.items() if k in current_keys
        }

        return smoothed

    def _trigger_recording_on_person_detection(self, camera_name):
        """Задейства запис при откриване на човек"""
        try:
            # Проверяваме дали recording модулът е наличен
            if (
                hasattr(self.app, "recording_module")
                and self.app.recording_module
                and hasattr(self.app, "RECORDING_MODULE_AVAILABLE")
                and self.app.RECORDING_MODULE_AVAILABLE
            ):
                # Намираме индекса на камерата
                camera_index = -1
                for i, camera in enumerate(self.app.cameras):
                    if camera["name"] == camera_name:
                        camera_index = i
                        break

                if camera_index >= 0:
                    # Проверяваме дали камерата има конфигурация за запис
                    camera = self.app.cameras[camera_index]
                    if "recording_config" in camera:
                        config = camera["recording_config"]

                        # Проверяваме дали записът при откриване на човек е активиран
                        if (
                            config["enable_recording"]
                            and config["record_mode"] == "person"
                        ):
                            # Задействаме записа
                            print(
                                f"[Tracking] Задействан запис при откриване на човек за камера: {camera_name}"
                            )

                            # Ако recording модулът има метод за обработка на кадър
                            if hasattr(
                                self.app.recording_module, "process_frame_for_recording"
                            ):
                                # Предаваме последния кадър за запис
                                if self.last_frame is not None:
                                    self.app.recording_module.process_frame_for_recording(
                                        camera_index, self.last_frame
                                    )

        except Exception as e:
            print(
                f"[Tracking] Грешка при задействане на запис при откриване на човек: {e}"
            )

    def _stop_recording_on_person_disappearance(self, camera_name):
        """Спира записа при изчезване на човек"""
        try:
            # Проверяваме дали recording модулът е наличен
            if (
                hasattr(self.app, "recording_module")
                and self.app.recording_module
                and hasattr(self.app, "RECORDING_MODULE_AVAILABLE")
                and self.app.RECORDING_MODULE_AVAILABLE
            ):
                # Намираме индекса на камерата
                camera_index = -1
                for i, camera in enumerate(self.app.cameras):
                    if camera["name"] == camera_name:
                        camera_index = i
                        break

                if camera_index >= 0:
                    # Спираме записа ако е активен
                    print(
                        f"[Tracking] Спиране на запис при изчезване на човек за камера: {camera_name}"
                    )
                    self.app.recording_module.stop_recording(camera_index)

        except Exception as e:
            print(f"[Tracking] Грешка при спиране на запис при изчезване на човек: {e}")

    def draw_detections(self, frame):
        try:
            # Запазваме последния кадър
            self.last_frame = frame.copy()

            current_objects = []  # Временен списък за текущите открития
            person_detected = False  # Флаг дали е открит човек

            if self.use_yolo and self.yolo_model:
                results = self.yolo_model.predict(
                    frame, conf=self.confidence_threshold, verbose=False
                )
                for result in results:
                    if hasattr(result, "boxes") and result.boxes is not None:
                        for box in result.boxes:
                            # Проверяваме дали имаме координати
                            if (
                                hasattr(box, "xyxy")
                                and box.xyxy is not None
                                and len(box.xyxy) > 0
                            ):
                                coords = box.xyxy[0].cpu().numpy()
                                x1, y1, x2, y2 = map(int, coords)
                                conf = (
                                    float(box.conf[0].cpu().numpy())
                                    if hasattr(box, "conf") and box.conf is not None
                                    else 0.0
                                )
                                cls_id = (
                                    int(box.cls[0].cpu().numpy())
                                    if hasattr(box, "cls") and box.cls is not None
                                    else 0
                                )

                                # Получаваме размерите на кадъра
                                h, w = frame.shape[:2]

                                # Ограничаваме координатите в рамките на кадъра
                                x1 = max(0, min(x1, w - 1))
                                y1 = max(0, min(y1, h - 1))
                                x2 = max(0, min(x2, w - 1))
                                y2 = max(0, min(y2, h - 1))

                                # Проверяваме дали правоъгълникът е валиден и има минимален размер
                                if (
                                    x2 > x1 + 5 and y2 > y1 + 5
                                ):  # Минимален размер 5x5 пиксела
                                    # Проверяваме дали моделът има атрибут names
                                    if (
                                        hasattr(self.yolo_model, "names")
                                        and self.yolo_model.names
                                    ):
                                        label = self.yolo_model.names.get(
                                            cls_id, str(cls_id)
                                        )
                                    else:
                                        label = str(cls_id)

                                    # Проверяваме дали е открит човек
                                    if label.lower() == "person":
                                        person_detected = True

                                    # Връщаме координатите директно в пространството на кадъра
                                    current_objects.append(
                                        (x1, y1, x2, y2, conf, label)
                                    )

            else:
                # Motion detection
                fg_mask = self.background_subtractor.apply(frame)
                kernel = cv2.getStructuringElement(cv2.MORPH_ELLIPSE, (5, 5))
                fg_mask = cv2.morphologyEx(fg_mask, cv2.MORPH_OPEN, kernel)
                contours, _ = cv2.findContours(
                    fg_mask, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE
                )
                for cnt in contours:
                    if cv2.contourArea(cnt) < self.motion_threshold:
                        continue
                    x, y, w, h = cv2.boundingRect(cnt)
                    # Получаваме размерите на кадъра
                    h_frame, w_frame = frame.shape[:2]

                    # Ограничаваме координатите в рамките на кадъра
                    x = max(0, min(x, w_frame - 1))
                    y = max(0, min(y, h_frame - 1))
                    w = max(10, min(w, w_frame - x))  # Минимална ширина 10 пиксела
                    h = max(10, min(h, h_frame - y))  # Минимална височина 10 пиксела

                    # Добавяме към текущите обекти
                    current_objects.append((x, y, x + w, y + h, 0.5, "motion"))

            # Прилагаме плавно проследяване
            self.detected_objects = self._smooth_coordinates(current_objects)

            # Проверяваме дали имаме текуща камера
            current_camera = self.app.get_current_camera()
            if current_camera:
                camera_name = current_camera["name"]

                # Ако е открит човек, задействаме записа
                if person_detected:
                    self._trigger_recording_on_person_detection(camera_name)
                    self.person_detected_flags[camera_name] = True
                    self.last_person_detection_time[camera_name] = time.time()
                else:
                    # Проверяваме дали човекът е бил открит и вече не е
                    if (
                        camera_name in self.person_detected_flags
                        and self.person_detected_flags[camera_name]
                    ):
                        # Проверяваме дали е изтекло времето за спиране на записа
                        if (
                            camera_name in self.last_person_detection_time
                            and time.time()
                            - self.last_person_detection_time[camera_name]
                            > 10
                        ):  # 10 секунди след изчезване
                            self.person_detected_flags[camera_name] = False
                            # Спираме записа при изчезване на човека
                            self._stop_recording_on_person_disappearance(camera_name)

            return frame

        except Exception as e:
            print(f"[Tracking] draw_detections error: {e}")
            traceback.print_exc()
            self.detected_objects = []
            return frame
