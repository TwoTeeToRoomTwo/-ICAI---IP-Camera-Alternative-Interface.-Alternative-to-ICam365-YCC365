# recording_module.py
import cv2
import os
import time
import threading
import json
from datetime import datetime, timedelta
from collections import deque
import pygame
import tkinter as tk
from tkinter import ttk, messagebox


class RecordingModule:
    def __init__(self, camera_controller):
        self.camera_controller = camera_controller
        self.recording_configs = {}
        self.recording_states = {}
        self.person_detected_timers = {}
        self.image_capture_timers = {}
        self.setup_recording_directories()

    def setup_recording_directories(self):
        """Създава директории за записи на всички камери"""
        for camera in self.camera_controller.cameras:
            self.create_camera_directories(camera)

    def create_camera_directories(self, camera):
        """Създава директории за конкретна камера"""
        if "name" in camera:
            base_dir = camera["name"]
            # Премахва невалидни символи от името на директорията
            base_dir = "".join(
                c if c.isalnum() or c in " _-" else "_" for c in base_dir
            )

            # Създава основната директория за камерата
            if not os.path.exists(base_dir):
                os.makedirs(base_dir)

            # Създава поддиректория за изображения
            images_dir = os.path.join(base_dir, "изображения")
            if not os.path.exists(images_dir):
                os.makedirs(images_dir)

    def update_camera_name_directories(self, old_name, new_name):
        """Актуализира имената на директориите при смяна на името на камера"""
        old_dir = "".join(c if c.isalnum() or c in " _-" else "_" for c in old_name)
        new_dir = "".join(c if c.isalnum() or c in " _-" else "_" for c in new_name)

        if os.path.exists(old_dir) and old_dir != new_dir:
            try:
                os.rename(old_dir, new_dir)
                print(f"Директорията е преименувана от {old_dir} на {new_dir}")
            except Exception as e:
                print(f"Грешка при преименуване на директория: {e}")

    def get_default_config(self):
        """Връща конфигурация по подразбиране"""
        return {
            "enable_recording": False,
            "enable_images": False,
            "record_mode": "continuous",  # continuous, scheduled, person
            "start_time": "00:00",
            "end_time": "23:59",
            "days": {
                "mon": True,
                "tue": True,
                "wed": True,
                "thu": True,
                "fri": True,
                "sat": True,
                "sun": True,
            },
            "pre_record_delay": 60,
            "stop_delay": 20,
            "min_photo_time": 60,
            "photo_count": 2,
            "photo_interval": 2,
            "video_retention": "7d",
            "image_retention": "24h",
            "max_space_gb": 100,
        }

    def is_scheduled_time(self, config):
        """Проверява дали текущото време е в рамките на графика за запис"""
        if config["record_mode"] != "scheduled":
            return True

        now = datetime.now()
        current_time = now.strftime("%H:%M")
        day_names = ["mon", "tue", "wed", "thu", "fri", "sat", "sun"]
        current_day = day_names[now.weekday()]

        # Проверка дали денят е активен
        if not config["days"].get(current_day, True):
            return False

        # Проверка на времевия диапазон
        start_time = config["start_time"]
        end_time = config["end_time"]

        return start_time <= current_time <= end_time

    def toggle_recording(self, camera_index):
        """Превключва записа за конкретна камера"""
        if camera_index < 0 or camera_index >= len(self.camera_controller.cameras):
            return

        camera = self.camera_controller.cameras[camera_index]
        camera_name = camera["name"]

        # Зарежда конфигурацията от камерата
        if "recording_config" not in camera:
            camera["recording_config"] = self.get_default_config()

        config = camera["recording_config"]
        config["enable_recording"] = not config["enable_recording"]

        # Актуализира конфигурацията в основното приложение
        self.camera_controller.apply_recording_settings(camera_name, config)

        if config["enable_recording"]:
            print(f"Записът е стартиран за камера: {camera_name}")
            # Стартира записа ако е необходимо
            if config["record_mode"] != "person":
                self.start_recording(camera_index)
        else:
            print(f"Записът е спрян за камера: {camera_name}")
            # Спира записа
            self.stop_recording(camera_index)

    def start_recording(self, camera_index):
        """Стартира запис на видео за конкретна камера"""
        if camera_index < 0 or camera_index >= len(self.camera_controller.cameras):
            return

        camera = self.camera_controller.cameras[camera_index]
        camera_name = camera["name"]

        if "recording_config" not in camera:
            camera["recording_config"] = self.get_default_config()

        config = camera["recording_config"]

        if not config["enable_recording"]:
            return

        # Проверка на графика
        if not self.is_scheduled_time(config):
            return

        # Инициализация на състоянието за запис
        if camera_index not in self.recording_states:
            self.recording_states[camera_index] = {
                "is_recording": False,
                "video_writer": None,
                "start_time": None,
                "frames_buffer": deque(maxlen=300),  # Буфер за предварителен запис
            }

    def stop_recording(self, camera_index):
        """Спира запис на видео за конкретна камера"""
        if camera_index in self.recording_states:
            state = self.recording_states[camera_index]
            if state["video_writer"]:
                try:
                    state["video_writer"].release()
                except Exception as e:
                    print(f"Грешка при спиране на запис: {e}")
            state["is_recording"] = False
            state["video_writer"] = None
            state["start_time"] = None

    def process_frame_for_recording(self, camera_index, frame):
        """Обработва кадър за запис"""
        if camera_index < 0 or camera_index >= len(self.camera_controller.cameras):
            return

        camera = self.camera_controller.cameras[camera_index]
        camera_name = camera["name"]

        if "recording_config" not in camera:
            camera["recording_config"] = self.get_default_config()

        config = camera["recording_config"]

        if not config["enable_recording"]:
            return

        # Проверка на графика
        if not self.is_scheduled_time(config):
            return

        # Проверка за запис при разпознаване на човек
        person_detected = self.is_person_detected_in_frame(camera_index)

        if config["record_mode"] == "person":
            self.handle_person_recording(camera_index, frame, person_detected, config)
        else:
            self.handle_continuous_recording(camera_index, frame, config)

    def is_person_detected_in_frame(self, camera_index):
        """Проверява дали в кадъра е разпознат човек"""
        # Проверява дали tracking модулът е наличен
        try:
            # Използва глобалната променлива TRACKING_MODULE_AVAILABLE
            global TRACKING_MODULE_AVAILABLE
            tracking_available = TRACKING_MODULE_AVAILABLE
        except NameError:
            # Ако не съществува, предполага че не е наличен
            tracking_available = False

        if (
            tracking_available
            and self.camera_controller.camera_tracker
            and hasattr(self.camera_controller.camera_tracker, "detected_objects")
        ):
            try:
                objects = self.camera_controller.camera_tracker.detected_objects
                for obj in objects:
                    if len(obj) >= 6 and str(obj[5]).lower() == "person":
                        return True
            except Exception as e:
                print(f"Грешка при проверка за разпознаване на човек: {e}")
        return False

    def handle_person_recording(self, camera_index, frame, person_detected, config):
        """Обработва запис при разпознаване на човек"""
        current_time = time.time()

        if person_detected:
            # Започва таймер при разпознаване на човек
            if camera_index not in self.person_detected_timers:
                self.person_detected_timers[camera_index] = current_time

            # Проверка дали е изминало времето за начало на запис
            if (
                current_time - self.person_detected_timers[camera_index]
                >= config["pre_record_delay"]
                and camera_index not in self.recording_states
            ):
                self.start_video_recording(camera_index, frame, config)

            # Проверка за заснемане на изображения
            if (
                current_time - self.person_detected_timers[camera_index]
                >= config["min_photo_time"]
                and camera_index not in self.image_capture_timers
            ):
                self.capture_images(camera_index, frame, config)
        else:
            # Нулира таймера ако човекът не е разпознат
            if camera_index in self.person_detected_timers:
                del self.person_detected_timers[camera_index]

            # Спира записа ако е активен и е изтекло времето
            if (
                camera_index in self.recording_states
                and current_time
                - self.recording_states[camera_index].get("last_person_time", 0)
                >= config["stop_delay"]
            ):
                self.stop_recording(camera_index)

    def handle_continuous_recording(self, camera_index, frame, config):
        """Обработва непрекъснат запис"""
        if camera_index not in self.recording_states:
            self.start_video_recording(camera_index, frame, config)
        else:
            self.write_frame_to_video(camera_index, frame)

    def start_video_recording(self, camera_index, frame, config):
        """Стартира запис на видео файл"""
        camera = self.camera_controller.cameras[camera_index]
        camera_name = camera["name"]

        # Създава директория ако не съществува
        base_dir = "".join(c if c.isalnum() or c in " _-" else "_" for c in camera_name)
        if not os.path.exists(base_dir):
            os.makedirs(base_dir)

        # Генерира име на файл
        timestamp = datetime.now().strftime("%d_%m_%Y_%H_%M")
        filename = f"{timestamp}.mp4"
        filepath = os.path.join(base_dir, filename)

        # Инициализира VideoWriter
        height, width = frame.shape[:2]
        fourcc = cv2.VideoWriter_fourcc(*"mp4v")
        fps = 10  # Според настройките на камерата

        try:
            video_writer = cv2.VideoWriter(filepath, fourcc, fps, (width, height))
            self.recording_states[camera_index] = {
                "is_recording": True,
                "video_writer": video_writer,
                "start_time": time.time(),
                "last_person_time": time.time(),
                "filepath": filepath,
            }

            # Записва буферираните кадри ако има
            if "frames_buffer" in self.recording_states[camera_index]:
                for buffered_frame in self.recording_states[camera_index][
                    "frames_buffer"
                ]:
                    video_writer.write(buffered_frame)

            print(f"Започна запис на видео: {filepath}")
        except Exception as e:
            print(f"Грешка при стартиране на запис: {e}")

    def write_frame_to_video(self, camera_index, frame):
        """Записва кадър във видео файл"""
        if (
            camera_index in self.recording_states
            and self.recording_states[camera_index]["is_recording"]
            and self.recording_states[camera_index]["video_writer"]
        ):
            try:
                self.recording_states[camera_index]["video_writer"].write(frame)
            except Exception as e:
                print(f"Грешка при запис на кадър: {e}")

    def capture_images(self, camera_index, frame, config):
        """Заснема серия от изображения"""
        camera = self.camera_controller.cameras[camera_index]
        camera_name = camera["name"]

        # Създава директория ако не съществува
        base_dir = "".join(c if c.isalnum() or c in " _-" else "_" for c in camera_name)
        images_dir = os.path.join(base_dir, "изображения")
        if not os.path.exists(images_dir):
            os.makedirs(images_dir)

        # Генерира име на файл
        timestamp = datetime.now().strftime("%d_%m_%Y_%H_%M")

        def capture_image_sequence(count, interval):
            for i in range(count):
                img_filename = f"{timestamp}_{i + 1}.jpeg"
                img_filepath = os.path.join(images_dir, img_filename)

                try:
                    # Запазва изображението с високо качество
                    success = cv2.imwrite(
                        img_filepath, frame, [cv2.IMWRITE_JPEG_QUALITY, 95]
                    )
                    if success:
                        print(f"Заснето изображение: {img_filepath}")
                    else:
                        print(f"Грешка при заснемане на изображение: {img_filepath}")
                except Exception as e:
                    print(f"Грешка при заснемане на изображение: {e}")

                if i < count - 1:  # Не чака след последното изображение
                    time.sleep(interval)

        # Стартира в отделна нишка за да не блокира основния поток
        thread = threading.Thread(
            target=capture_image_sequence,
            args=(config["photo_count"], config["photo_interval"]),
        )
        thread.daemon = True
        thread.start()

        # Маркира че изображенията са заснети
        self.image_capture_timers[camera_index] = time.time()

    def cleanup_old_files(self, camera_name, retention_period, is_video=True):
        """Изтрива стари файлове според зададения период"""
        base_dir = "".join(c if c.isalnum() or c in " _-" else "_" for c in camera_name)

        if is_video:
            search_dir = base_dir
        else:
            search_dir = os.path.join(base_dir, "изображения")

        if not os.path.exists(search_dir):
            return

        # Изчислява cutoff време
        now = datetime.now()
        if retention_period == "12h":
            cutoff_time = now - timedelta(hours=12)
        elif retention_period == "24h":
            cutoff_time = now - timedelta(hours=24)
        elif retention_period == "1d":
            cutoff_time = now - timedelta(days=1)
        elif retention_period == "7d":
            cutoff_time = now - timedelta(days=7)
        elif retention_period == "30d":
            cutoff_time = now - timedelta(days=30)
        elif retention_period == "90d":
            cutoff_time = now - timedelta(days=90)
        elif retention_period == "never":
            return  # never - не изтрива нищо
        else:
            return

        # Изтрива стари файлове
        for filename in os.listdir(search_dir):
            filepath = os.path.join(search_dir, filename)
            if os.path.isfile(filepath):
                file_time = datetime.fromtimestamp(os.path.getctime(filepath))
                if file_time < cutoff_time:
                    try:
                        os.remove(filepath)
                        print(f"Изтрит стар файл: {filepath}")
                    except Exception as e:
                        print(f"Грешка при изтриване на файл {filepath}: {e}")

    def confirm_delete_all_recordings(self):
        """Показва диалог за потвърждение за изтриване на всички записи"""
        try:
            # Създава Tkinter прозорец за потвърждение
            root = tk.Tk()
            root.withdraw()  # Скрива главния прозорец

            result = messagebox.askyesno(
                "Потвърждение",
                "Сигурни ли сте, че искате да изтриете ВСИЧКИ записи?",
                icon="warning",
            )

            root.destroy()
            return result
        except Exception as e:
            print(f"Грешка при диалог за потвърждение: {e}")
            return False

    def delete_all_recordings(self):
        """Изтрива всички записи от всички камери след потвърждение"""
        # Показва диалог за потвърждение
        if self.confirm_delete_all_recordings():
            for camera in self.camera_controller.cameras:
                camera_name = camera["name"]
                base_dir = "".join(
                    c if c.isalnum() or c in " _-" else "_" for c in camera_name
                )

                if os.path.exists(base_dir):
                    try:
                        # Изтрива видео файлове
                        for filename in os.listdir(base_dir):
                            if filename.endswith(".mp4"):
                                filepath = os.path.join(base_dir, filename)
                                os.remove(filepath)

                        # Изтрива изображения
                        images_dir = os.path.join(base_dir, "изображения")
                        if os.path.exists(images_dir):
                            for filename in os.listdir(images_dir):
                                if filename.endswith(".jpeg"):
                                    filepath = os.path.join(images_dir, filename)
                                    os.remove(filepath)

                        print(f"Изтрити всички записи за камера: {camera_name}")
                    except Exception as e:
                        print(f"Грешка при изтриване на записи за {camera_name}: {e}")
            print("Всички записи са изтрити")
        else:
            print("Изтриването е отказано")

    def show_recording_settings_gui(self):
        """Показва GUI за настройки на запис"""
        # Създава нова нишка за GUI за да не блокира основното приложение
        gui_thread = threading.Thread(target=self._create_settings_window)
        gui_thread.daemon = True
        gui_thread.start()

    def _create_settings_window(self):
        """Създава прозорец с настройки за запис"""
        try:
            # Създава Tkinter прозорец
            root = tk.Tk()
            root.title("Настройки на Записи")
            root.geometry("600x700")
            root.resizable(True, True)

            # Избрана камера
            current_camera = self.camera_controller.get_current_camera()
            if not current_camera:
                messagebox.showerror("Грешка", "Няма избрана камера")
                root.destroy()
                return

            camera_name = current_camera["name"]

            # Зарежда конфигурацията от камерата
            if "recording_config" not in current_camera:
                current_camera["recording_config"] = self.get_default_config()

            config = current_camera["recording_config"]

            # Заглавие
            title_label = tk.Label(
                root,
                text=f"Настройки за запис - {camera_name}",
                font=("Arial", 14, "bold"),
            )
            title_label.pack(pady=10)

            # Notebook за табове
            notebook = ttk.Notebook(root)
            notebook.pack(fill="both", expand=True, padx=10, pady=5)

            # Основни настройки таб
            basic_frame = ttk.Frame(notebook)
            notebook.add(basic_frame, text="Основни")

            # Активиране на запис
            enable_frame = ttk.Frame(basic_frame)
            enable_frame.pack(fill="x", padx=10, pady=5)

            enable_var = tk.BooleanVar(value=config["enable_recording"])
            enable_check = ttk.Checkbutton(
                enable_frame, text="Активиране на запис на видео", variable=enable_var
            )
            enable_check.pack(side="left")

            # Активиране на изображения
            images_var = tk.BooleanVar(value=config["enable_images"])
            images_check = ttk.Checkbutton(
                basic_frame,
                text="Активиране на запис на изображения",
                variable=images_var,
            )
            images_check.pack(padx=10, pady=5, anchor="w")

            # Режим на запис
            mode_frame = ttk.LabelFrame(basic_frame, text="Режим на запис")
            mode_frame.pack(fill="x", padx=10, pady=5)

            mode_var = tk.StringVar(value=config["record_mode"])
            ttk.Radiobutton(
                mode_frame,
                text="Непрекъснат запис",
                variable=mode_var,
                value="continuous",
            ).pack(anchor="w", padx=5, pady=2)
            ttk.Radiobutton(
                mode_frame, text="По график", variable=mode_var, value="scheduled"
            ).pack(anchor="w", padx=5, pady=2)
            ttk.Radiobutton(
                mode_frame,
                text="Само при разпознат човек",
                variable=mode_var,
                value="person",
            ).pack(anchor="w", padx=5, pady=2)

            # График таб
            schedule_frame = ttk.Frame(notebook)
            notebook.add(schedule_frame, text="График")

            # Начален и краен час
            time_frame = ttk.LabelFrame(schedule_frame, text="Време на запис")
            time_frame.pack(fill="x", padx=10, pady=5)

            ttk.Label(time_frame, text="Начален час:").grid(
                row=0, column=0, padx=5, pady=5, sticky="w"
            )
            start_hour_var = tk.StringVar(value=config["start_time"].split(":")[0])
            start_minute_var = tk.StringVar(value=config["start_time"].split(":")[1])
            ttk.Spinbox(
                time_frame, from_=0, to=23, width=5, textvariable=start_hour_var
            ).grid(row=0, column=1, padx=5, pady=5)
            ttk.Label(time_frame, text=":").grid(row=0, column=2, pady=5)
            ttk.Spinbox(
                time_frame, from_=0, to=59, width=5, textvariable=start_minute_var
            ).grid(row=0, column=3, padx=5, pady=5)

            ttk.Label(time_frame, text="Краен час:").grid(
                row=1, column=0, padx=5, pady=5, sticky="w"
            )
            end_hour_var = tk.StringVar(value=config["end_time"].split(":")[0])
            end_minute_var = tk.StringVar(value=config["end_time"].split(":")[1])
            ttk.Spinbox(
                time_frame, from_=0, to=23, width=5, textvariable=end_hour_var
            ).grid(row=1, column=1, padx=5, pady=5)
            ttk.Label(time_frame, text=":").grid(row=1, column=2, pady=5)
            ttk.Spinbox(
                time_frame, from_=0, to=59, width=5, textvariable=end_minute_var
            ).grid(row=1, column=3, padx=5, pady=5)

            # Дни на седмицата
            days_frame = ttk.LabelFrame(schedule_frame, text="Дни на седмицата")
            days_frame.pack(fill="x", padx=10, pady=5)

            days_vars = {}
            day_names = [
                "Понеделник",
                "Вторник",
                "Сряда",
                "Четвъртък",
                "Петък",
                "Събота",
                "Неделя",
            ]
            day_keys = ["mon", "tue", "wed", "thu", "fri", "sat", "sun"]

            for i, (day_name, day_key) in enumerate(zip(day_names, day_keys)):
                var = tk.BooleanVar(value=config["days"].get(day_key, True))
                days_vars[day_key] = var
                ttk.Checkbutton(days_frame, text=day_name, variable=var).grid(
                    row=i // 4, column=i % 4, padx=5, pady=2, sticky="w"
                )

            # Разпознаване таб
            detection_frame = ttk.Frame(notebook)
            notebook.add(detection_frame, text="Разпознаване")

            # Забавяне преди запис
            delay_frame = ttk.LabelFrame(
                detection_frame, text="Забавяне преди запис (секунди)"
            )
            delay_frame.pack(fill="x", padx=10, pady=5)

            pre_record_var = tk.IntVar(value=config["pre_record_delay"])
            ttk.Spinbox(
                delay_frame, from_=0, to=300, width=10, textvariable=pre_record_var
            ).pack(padx=5, pady=5)

            # Време за прекратяване
            stop_delay_frame = ttk.LabelFrame(
                detection_frame, text="Време за прекратяване (секунди)"
            )
            stop_delay_frame.pack(fill="x", padx=10, pady=5)

            stop_delay_var = tk.IntVar(value=config["stop_delay"])
            ttk.Spinbox(
                stop_delay_frame, from_=5, to=120, width=10, textvariable=stop_delay_var
            ).pack(padx=5, pady=5)

            # Минимално време за снимки
            photo_time_frame = ttk.LabelFrame(
                detection_frame, text="Минимално време за снимки (секунди)"
            )
            photo_time_frame.pack(fill="x", padx=10, pady=5)

            min_photo_var = tk.IntVar(value=config["min_photo_time"])
            ttk.Spinbox(
                photo_time_frame, from_=30, to=600, width=10, textvariable=min_photo_var
            ).pack(padx=5, pady=5)

            # Брой снимки
            photo_count_frame = ttk.LabelFrame(detection_frame, text="Брой снимки")
            photo_count_frame.pack(fill="x", padx=10, pady=5)

            photo_count_var = tk.IntVar(value=config["photo_count"])
            ttk.Spinbox(
                photo_count_frame,
                from_=1,
                to=10,
                width=10,
                textvariable=photo_count_var,
            ).pack(padx=5, pady=5)

            # Интервал между снимките
            photo_interval_frame = ttk.LabelFrame(
                detection_frame, text="Интервал между снимките (секунди)"
            )
            photo_interval_frame.pack(fill="x", padx=10, pady=5)

            photo_interval_var = tk.IntVar(value=config["photo_interval"])
            ttk.Spinbox(
                photo_interval_frame,
                from_=1,
                to=10,
                width=10,
                textvariable=photo_interval_var,
            ).pack(padx=5, pady=5)

            # Управление на съхранение таб
            storage_frame = ttk.Frame(notebook)
            notebook.add(storage_frame, text="Съхранение")

            # Автоматично изтриване на видео записи
            video_retention_frame = ttk.LabelFrame(
                storage_frame, text="Автоматично изтриване на видео записи"
            )
            video_retention_frame.pack(fill="x", padx=10, pady=5)

            video_retention_var = tk.StringVar(value=config["video_retention"])
            video_retention_combo = ttk.Combobox(
                video_retention_frame,
                textvariable=video_retention_var,
                values=["1d", "3d", "7d", "30d", "90d", "never"],
            )
            video_retention_combo.pack(padx=5, pady=5, fill="x")

            # Автоматично изтриване на изображения
            image_retention_frame = ttk.LabelFrame(
                storage_frame, text="Автоматично изтриване на изображения"
            )
            image_retention_frame.pack(fill="x", padx=10, pady=5)

            image_retention_var = tk.StringVar(value=config["image_retention"])
            image_retention_combo = ttk.Combobox(
                image_retention_frame,
                textvariable=image_retention_var,
                values=["12h", "24h", "7d", "30d", "never"],
            )
            image_retention_combo.pack(padx=5, pady=5, fill="x")

            # Максимално използвано пространство
            space_frame = ttk.LabelFrame(
                storage_frame, text="Максимално използвано пространство (GB)"
            )
            space_frame.pack(fill="x", padx=10, pady=5)

            max_space_var = tk.IntVar(value=config["max_space_gb"])
            ttk.Spinbox(
                space_frame, from_=10, to=1000, width=10, textvariable=max_space_var
            ).pack(padx=5, pady=5)

            # Бутони
            button_frame = ttk.Frame(root)
            button_frame.pack(fill="x", padx=10, pady=10)

            def save_settings():
                # Събира всички настройки
                new_config = {
                    "enable_recording": enable_var.get(),
                    "enable_images": images_var.get(),
                    "record_mode": mode_var.get(),
                    "start_time": f"{start_hour_var.get().zfill(2)}:{start_minute_var.get().zfill(2)}",
                    "end_time": f"{end_hour_var.get().zfill(2)}:{end_minute_var.get().zfill(2)}",
                    "days": {key: var.get() for key, var in days_vars.items()},
                    "pre_record_delay": pre_record_var.get(),
                    "stop_delay": stop_delay_var.get(),
                    "min_photo_time": min_photo_var.get(),
                    "photo_count": photo_count_var.get(),
                    "photo_interval": photo_interval_var.get(),
                    "video_retention": video_retention_var.get(),
                    "image_retention": image_retention_var.get(),
                    "max_space_gb": max_space_var.get(),
                }

                # Запазва настройките в камерата
                current_camera["recording_config"] = new_config

                # Прилага настройките в основното приложение
                self.camera_controller.apply_recording_settings(camera_name, new_config)

                # Запазва конфигурацията
                self.camera_controller.save_config()

                messagebox.showinfo("Успех", "Настройките са запазени успешно!")
                root.destroy()

            def cancel_settings():
                root.destroy()

            ttk.Button(button_frame, text="Запази", command=save_settings).pack(
                side="left", padx=5
            )
            ttk.Button(button_frame, text="Отказ", command=cancel_settings).pack(
                side="left", padx=5
            )

            # Центрира прозореца
            root.update_idletasks()
            x = (root.winfo_screenwidth() // 2) - (root.winfo_width() // 2)
            y = (root.winfo_screenheight() // 2) - (root.winfo_height() // 2)
            root.geometry(f"+{x}+{y}")

            root.mainloop()

        except Exception as e:
            print(f"Грешка при създаване на GUI за настройки: {e}")
