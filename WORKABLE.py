# IM TOO LAZY, TO TRANSLATE, ALL OF THE TEXT, OF THE EXPLANATIONS. SO GOOD LUCK WITH THAT TASK :P

import pygame
import os

os.environ["OPENCV_LOG_LEVEL"] = "ERROR"
os.environ["GST_DEBUG"] = "0"

import cv2
import threading
import requests
import time
from datetime import datetime
import json
import numpy as np
from pygame import gfxdraw
import subprocess
import signal
import sys
import re
import gc
import traceback
import socket

# Заглушаваме OpenCV логовете
os.environ["OPENCV_LOG_LEVEL"] = "SILENT"

try:
    import sounddevice as sd
    from scipy.io.wavfile import write as wav_write

    WALKIE_TALKIE_AVAILABLE = True
except ImportError as e:
    print(f"Warning: walkie-talkie dependencies missing: {e}")
    WALKIE_TALKIE_AVAILABLE = False


class CameraController:
    def __init__(self):
        # === Основни променливи за Intercom ===
        self.walkie_talkie_recording = False
        self.walkie_talkie_audio_data = []
        self.walkie_talkie_start_time = None
        self.walkie_talkie_button_locked = False
        self.mic_gain = 6
        self.playback_gain = 6
        self.walkie_talkie_animation_start = None
        self.walkie_talkie_active = False
        self.ptz_x = "?"
        self.ptz_y = "?"

        self.ptz_cache = {}
        self.storage_cache = {}
        self.show_recordings_window
        self.recordings_window_open = False
        self.recordings_process = None

        self.alarm_triggered = False

        # Инициализация на Pygame
        pygame.init()
        try:
            pygame.mixer.init(frequency=8000, size=-16, channels=1, buffer=64)
        except Exception as e:
            print("Warning: mixer init failed:", e)

        # Начални размери
        self.screen_width = 1200
        self.screen_height = 800

        self.screen = pygame.display.set_mode(
            (self.screen_width, self.screen_height),
            pygame.RESIZABLE | pygame.DOUBLEBUF | pygame.HWSURFACE,
        )
        pygame.display.set_caption("IP Камера Контрол - GStreamer")

        # Цветова палитра
        self.colors = {
            "background": (25, 25, 35),
            "panel": (35, 35, 45),
            "accent": (70, 130, 180),
            "accent_hover": (100, 160, 210),
            "success": (46, 204, 113),
            "warning": (241, 196, 15),
            "danger": (231, 76, 60),
            "text": (240, 240, 240),
            "text_secondary": (180, 180, 180),
            "border": (60, 60, 70),
            "walkie_idle": (180, 150, 220),
            "walkie_active": (30, 50, 120),
        }

        # Шрифтове
        pygame.font.init()
        self.font_large = pygame.font.SysFont("Arial", 14, bold=True)
        self.font_medium = pygame.font.SysFont("Arial", 12, bold=True)
        self.font_small = pygame.font.SysFont("Arial", 10, bold=True)
        self.font_bold = pygame.font.SysFont("Arial", 12, bold=True)

        # Видеонастройки
        self.max_zoom = 5.0
        self.zoom_step = 0.2
        self.current_zoom = 1.0

        # Fullscreen
        self.fullscreen_mode = False
        self.fullscreen_surface = None

        # UI state
        self.video_offset_x = 0
        self.video_offset_y = 0
        self.video_surface_width = 0
        self.video_surface_height = 0

        # Конфиг файл
        self.config_file = "camera_config.json"

        # Buttons threading state
        self.pressed_buttons = {}
        self.button_press_times = {}
        self.button_threads = {}
        self.button_cooldowns = {}

        # Movement control flags
        self.stop_all_movements_flag = False

        # Running
        self.running = True

        # Lock for thread synchronization
        self.position_lock = threading.Lock()
        self.camera_lock = threading.RLock()

        # Key mapping for keyboard controls
        self.key_map = {
            pygame.K_SPACE: "0",
            pygame.K_UP: "3",
            pygame.K_w: "3",
            pygame.K_DOWN: "4",
            pygame.K_s: "4",
            pygame.K_LEFT: "1",
            pygame.K_a: "1",
            pygame.K_RIGHT: "2",
            pygame.K_d: "2",
            pygame.K_KP_PLUS: "9",
            pygame.K_PLUS: "9",
            pygame.K_KP_MINUS: "a",
            pygame.K_MINUS: "a",
        }

        # Audio process
        self.audio_process = None
        self.audio_process_pid = None
        self.audio_volume = 75

        # Movement blocking
        self.movement_blocking_enabled = True

        # Session for HTTP requests
        self.http_session = requests.Session()
        adapter = requests.adapters.HTTPAdapter(
            pool_connections=10, pool_maxsize=10, max_retries=1
        )
        self.http_session.mount("http://", adapter)

        # Input fields
        self.ip_input = ""
        self.name_input = ""
        self.input_active = None

        # UI status
        self.status_message = "Готов за работа"
        self.status_timer = time.time()

        # Video surfaces
        self.video_surface = None
        self.video_rect = None
        self.mini_camera_rects = {}
        self.last_frame = None

        # White light off timer
        self.white_light_off_timer = None

        # Камери
        self.cameras = []
        self.current_camera_index = -1

        # Connection management
        self.camera_connectivity_states = {}
        self.connectivity_check_time = time.time()
        self.connectivity_check_interval = 60

        # Storage cache
        self.storage_cache = {}
        self.storage_cache_timestamp = {}
        self.storage_cache_update_interval = 40

        # Зареждаме конфигурацията
        self.load_config()

        # Сигнал handler
        signal.signal(signal.SIGINT, self.signal_handler)
        signal.signal(signal.SIGTERM, self.signal_handler)

        # Стартираме първоначални опити за свързване
        self.initial_connection_attempts()

        # Start background connectivity checker
        self.start_connectivity_checker()

        # Start storage cache updater
        self.start_storage_cache_updater()

        self.main_loop()

    def start_connectivity_checker(self):
        """Starts a background thread to check connectivity periodically"""

        def connectivity_worker():
            while self.running:
                try:
                    current_time = time.time()

                    # Check if it's time to perform connectivity checks
                    if (
                        current_time - self.connectivity_check_time
                        >= self.connectivity_check_interval
                    ):
                        # Get offline cameras sorted by last octet of IP address
                        offline_cameras = []
                        for i, camera in enumerate(self.cameras):
                            if not camera.get("connected", False):
                                ip_octets = camera["ip"].split(".")
                                if len(ip_octets) >= 4:
                                    try:
                                        last_octet = int(ip_octets[-1])
                                        offline_cameras.append((last_octet, i, camera))
                                    except ValueError:
                                        # If IP parsing fails, just append with a high number
                                        offline_cameras.append((999, i, camera))

                        # Sort by last octet
                        offline_cameras.sort(key=lambda x: x[0])

                        # Attempt connections one by one with delays
                        for _, idx, camera in offline_cameras:
                            if not self.running:
                                break

                            # Mark as attempting connection
                            self.camera_connectivity_states[idx] = {
                                "attempting": True,
                                "start_time": time.time(),
                            }

                            # Try to connect
                            self.attempt_connection(idx)

                            # Remove the state after connection attempt
                            if idx in self.camera_connectivity_states:
                                del self.camera_connectivity_states[idx]

                            # Wait 10 seconds before next attempt
                            time.sleep(10)

                        # Update the last check time
                        self.connectivity_check_time = current_time

                except Exception as e:
                    print(f"Connectivity checker error: {e}")

                time.sleep(1)  # Check once per second for timing

        thread = threading.Thread(target=connectivity_worker, daemon=True)
        thread.start()

    def play_alarm(self):
        """Изпраща само една команда за аларма при едно натискане."""

        # Не изпращаме нова команда, ако вече е задействана
        if self.alarm_triggered:
            return

        self.alarm_triggered = True

        def worker():
            try:
                cam = self.get_current_camera()
                if cam is None:
                    self.alarm_triggered = False
                    return

                ports = [8001]
                success = False

                for port in ports:
                    try:
                        url = f"http://{cam['ip']}:{port}/playaudio"

                        response = self.http_session.get(
                            url,
                            params={"file": "/home/alarm.wav"},
                            timeout=1,
                        )

                        if response.status_code == 200:
                            success = True
                            self.set_status(f"Алармата е задействана на порт {port}")
                            break

                        print(
                            f"Грешка при playaudio на порт {port}: "
                            f"{response.status_code}"
                        )

                    except requests.exceptions.ConnectionError:
                        print(f"Няма връзка към порт {port}")

                    except Exception as e:
                        print(f"Грешка при playaudio на порт {port}: {e}")

                if not success:
                    self.alarm_triggered = False
                    self.connection_lost = True
                    self.set_status("Грешка: алармата не може да бъде задействана")

            except Exception as e:
                self.alarm_triggered = False
                print(f"Обща грешка при play_alarm: {e}")
                self.set_status("Грешка при активиране на алармата")

        threading.Thread(target=worker, daemon=True).start()

    def start_storage_cache_updater(self):
        """Starts a background thread to update storage cache periodically"""

        def storage_worker():
            while self.running:
                try:
                    current_time = time.time()

                    # Update storage for current camera
                    current_cam = self.get_current_camera()
                    if current_cam:
                        cam_ip = current_cam["ip"]

                        # Check if we need to update cache
                        last_update = self.storage_cache_timestamp.get(cam_ip, 0)

                        if (
                            current_time - last_update
                            >= self.storage_cache_update_interval
                        ):
                            try:
                                # Взимаме суровите данни в KB
                                cmd = (
                                    f"ssh root@{cam_ip} "
                                    '"df -k /dev/mmcblk0p1 | tail -n 1"'
                                )

                                result = subprocess.run(
                                    cmd,
                                    shell=True,
                                    capture_output=True,
                                    text=True,
                                    timeout=10,
                                )

                                if result.returncode == 0:
                                    line = result.stdout.strip()

                                    if line:
                                        parts = line.split()

                                        if len(parts) >= 5:
                                            total_kb = int(parts[1])
                                            used_kb = int(parts[2])
                                            avail_kb = int(parts[3])
                                            percent = parts[4]

                                            total_gb = total_kb / 1024 / 1024
                                            used_gb = used_kb / 1024 / 1024
                                            avail_gb = avail_kb / 1024 / 1024

                                            # Ако е под 1 GB показваме MB
                                            if used_gb < 1:
                                                used_str = f"{used_kb / 1024:.1f}MB"
                                            else:
                                                used_str = f"{used_gb:.2f}GB"

                                            self.storage_cache[cam_ip] = (
                                                f"заето {percent} "
                                                f"({used_str}) "
                                                f"от общо {total_gb:.2f}GB "
                                                f"(свободни {avail_gb:.2f}GB)"
                                            )

                                            self.storage_cache_timestamp[cam_ip] = (
                                                current_time
                                            )

                                        else:
                                            self.storage_cache[cam_ip] = (
                                                "невалиDay формат на df"
                                            )
                                            self.storage_cache_timestamp[cam_ip] = (
                                                current_time
                                            )

                                    else:
                                        self.storage_cache[cam_ip] = "няма данни"
                                        self.storage_cache_timestamp[cam_ip] = (
                                            current_time
                                        )

                                else:
                                    self.storage_cache[cam_ip] = (
                                        f"грешка при извличане: {result.stderr.strip()}"
                                    )
                                    self.storage_cache_timestamp[cam_ip] = current_time

                            except subprocess.TimeoutExpired:
                                self.storage_cache[cam_ip] = "таймаут при извличане"
                                self.storage_cache_timestamp[cam_ip] = current_time

                            except Exception as e:
                                self.storage_cache[cam_ip] = f"грешка: {str(e)}"
                                self.storage_cache_timestamp[cam_ip] = current_time

                except Exception as e:
                    print(f"Storage cache updater error: {e}")

                time.sleep(60)

        thread = threading.Thread(target=storage_worker, daemon=True)
        thread.start()

    def get_storage_info(self):
        """Returns storage information from cache"""
        current_cam = self.get_current_camera()
        if current_cam:
            cam_ip = current_cam["ip"]
            return self.storage_cache.get(cam_ip, "няма информация")
        return "няма избрана камера"

    def get_ptz_info(self):
        """Връща PTZ координатите от кеша"""

        current_cam = self.get_current_camera()

        if current_cam:
            cam_ip = current_cam["ip"]

            return self.ptz_cache.get(cam_ip, "X=? Y=?")

        return "X=? Y=?"

    def open_recordings_browser(self):
        """Отваря FTP файловия мениджър."""

        current_cam = self.get_current_camera()

        if not current_cam:
            messagebox.showerror("Грешка", "Първо изберете камера.")
            return

        RecordingsBrowser(parent=self.root, camera=current_cam)

    def show_recordings_window(self):
        """
        Стартира отделния файлов мениджър за записите.
        Не позволява стартирането на повече от един процес.
        """

        # Ако процесът съществува и все още работи,
        # не стартираме втори прозорец
        if (
            self.recordings_process is not None
            and self.recordings_process.poll() is None
        ):
            print("Прозорецът със записите вече е отворен.")
            return

        current_cam = self.get_current_camera()

        if not current_cam:
            print("Няма избрана камера.")
            return

        cam_ip = current_cam.get("ip")

        if not cam_ip:
            print("Избраната камера няма IP адрес.")
            return

        try:
            script_directory = os.path.dirname(os.path.abspath(__file__))

            browser_script = os.path.join(script_directory, "recordings_browser.py")

            self.recordings_process = subprocess.Popen(
                [
                    sys.executable,
                    browser_script,
                    cam_ip,
                ],
                cwd=script_directory,
            )

            print("Файловият мениджър за записите е стартиран.")

        except Exception as e:
            self.recordings_process = None
            print(f"Грешка при стартиране на файловия мениджър: {e}")

    def walkie_talkie_record_callback(self, indata, frames, time_info, status):
        if self.walkie_talkie_recording:
            scaled = np.clip(indata.copy() * (self.mic_gain / 100.0), -32768, 32767)
            self.walkie_talkie_audio_data.append(scaled.astype(np.int16))

    def walkie_talkie_start_recording(self):
        if not WALKIE_TALKIE_AVAILABLE:
            self.set_status("Intercom: липсват зависимости")
            return
        if self.walkie_talkie_recording or self.walkie_talkie_button_locked:
            return
        self.walkie_talkie_button_locked = True
        self.walkie_talkie_recording = True
        self.walkie_talkie_active = True
        self.walkie_talkie_animation_start = time.time()
        self.walkie_talkie_audio_data = []
        self.set_status("ГОВОРИ СЕГА...")

        def record_worker():
            try:
                with sd.InputStream(
                    samplerate=8000,
                    channels=1,
                    dtype="int16",
                    callback=self.walkie_talkie_record_callback,
                ):
                    start = time.time()
                    while self.walkie_talkie_recording and (time.time() - start < 20):
                        time.sleep(0.05)
            except Exception as e:
                print("Walkie-talkie record error:", e)
            finally:
                self.walkie_talkie_recording = False
                self.walkie_talkie_upload_and_play()

        threading.Thread(target=record_worker, daemon=True).start()

    def walkie_talkie_stop_recording(self):
        self.walkie_talkie_recording = False
        self.walkie_talkie_active = False
        self.walkie_talkie_button_locked = False

    def walkie_talkie_upload_and_play(self):
        if not self.walkie_talkie_audio_data:
            self.walkie_talkie_button_locked = False
            return

        cam = self.get_current_camera()
        if not cam:
            self.set_status("Няма активна камера")
            self.walkie_talkie_button_locked = False
            return

        CAMERA_IP = cam["ip"]
        LOCAL_DIR = os.path.join(os.path.dirname(__file__), "talking")
        os.makedirs(LOCAL_DIR, exist_ok=True)
        LOCAL_FILE = os.path.join(LOCAL_DIR, "rec.wav")
        REMOTE_FILE = "/tmp/mnt/talk/rec.wav"

        try:
            data = np.concatenate(self.walkie_talkie_audio_data, axis=0)
            data = np.clip(data * (self.playback_gain / 100.0), -32768, 32767).astype(
                np.int16
            )
            wav_write(LOCAL_FILE, 8000, data)

            # SSH upload
            with open(LOCAL_FILE, "rb") as f:
                subprocess.run(
                    ["ssh", f"root@{CAMERA_IP}", "-p", "22", f"cat > {REMOTE_FILE}"],
                    input=f.read(),
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    timeout=5,
                )

            # Play via CGI
            requests.get(
                f"http://{CAMERA_IP}:8001/playaudio?file={REMOTE_FILE}", timeout=10
            )

            duration = len(data) / 8000
            time.sleep(duration + 0.3)

            # Cleanup
            subprocess.run(
                ["ssh", f"root@{CAMERA_IP}", "-p", "22", f"rm -f {REMOTE_FILE}"],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=3,
            )
            if os.path.exists(LOCAL_FILE):
                os.remove(LOCAL_FILE)

        except Exception as e:
            print("Walkie-talkie playback error:", e)
            self.set_status("Грешка при възпроизвеждане")
        finally:
            self.walkie_talkie_button_locked = False

    def draw_walkie_talkie_button(self, surface, x, y, width, height):
        mouse_pos = pygame.mouse.get_pos()
        mouse_pressed = pygame.mouse.get_pressed()[0]
        rect = pygame.Rect(x, y, width, height)

        is_hovered = rect.collidepoint(mouse_pos)
        color = self.colors["walkie_idle"]

        if self.walkie_talkie_active:
            elapsed = time.time() - self.walkie_talkie_animation_start
            progress = min(elapsed / 15.0, 1.0)
            r = int(
                self.colors["walkie_active"][0] * (1 - progress)
                + self.colors["walkie_idle"][0] * progress
            )
            g = int(
                self.colors["walkie_active"][1] * (1 - progress)
                + self.colors["walkie_idle"][1] * progress
            )
            b = int(
                self.colors["walkie_active"][2] * (1 - progress)
                + self.colors["walkie_idle"][2] * progress
            )
            color = (r, g, b)
        elif is_hovered:
            color = tuple(min(255, c + 30) for c in self.colors["walkie_idle"])

        pygame.draw.rect(surface, color, rect, border_radius=8)
        pygame.draw.rect(surface, self.colors["border"], rect, 2, border_radius=8)

        text = "ГОВОРИ СЕГА" if self.walkie_talkie_active else "Intercom"
        text_surf = self.font_medium.render(text, True, self.colors["text"])
        surface.blit(text_surf, text_surf.get_rect(center=rect.center))

        # Handle press/release
        if (
            rect.collidepoint(mouse_pos)
            and mouse_pressed
            and not self.walkie_talkie_button_locked
        ):
            if not self.walkie_talkie_active:
                self.walkie_talkie_start_recording()
        elif self.walkie_talkie_active and not mouse_pressed:
            self.walkie_talkie_stop_recording()

    def signal_handler(self, signum, frame):
        print(f"Получен сигнал {signum}, спиране на приложението...")
        self.cleanup_and_exit()

    def cleanup_and_exit(self):
        print("Изчистване преди изход...")
        self.running = False

        # Спираме всички движения
        self.stop_all_movements()

        # Спираме аудио процеса
        self.stop_audio_stream()

        # Спираме всички потоци за камери
        for camera in self.cameras:
            try:
                if camera.get("cap"):
                    camera["cap"].release()
                    camera["cap"] = None
                if camera.get("mini_cap"):
                    camera["mini_cap"].release()
                    camera["mini_cap"] = None
            except Exception as e:
                print(f"Error releasing camera cap: {e}")

        # Release pygame resources safely
        try:
            pygame.quit()
        except Exception as e:
            print(f"Error quitting pygame: {e}")

        print("Приложението е спряно коректно")
        try:
            sys.exit(0)
        except SystemExit:
            os._exit(0)

    def load_config(self):
        try:
            if os.path.exists(self.config_file):
                with open(self.config_file, "r") as f:
                    config = json.load(f)

                self.movement_blocking_enabled = config.get(
                    "movement_blocking_enabled", self.movement_blocking_enabled
                )
                self.audio_volume = config.get("audio_volume", self.audio_volume)

                saved_cameras = config.get("cameras", [])
                if saved_cameras:
                    self.cameras = []
                    for cam in saved_cameras:
                        cam_obj = {
                            "ip": cam.get("ip"),
                            "name": cam.get("name", f"Камера {len(self.cameras) + 1}"),
                            "connected": False,
                            "rtsp_url": cam.get("rtsp_url", ""),
                            "audio_url": cam.get("audio_url", ""),
                            "cap": None,
                            "mini_cap": None,
                            "video_surface": None,
                            "mini_video_surface": None,
                            "white_light_status": cam.get("white_light_status", False),
                            "ir_light_status": cam.get("ir_light_status", False),
                            "day_night_status": cam.get("day_night_status", True),
                            "last_connection_attempt": 0,
                            "connection_attempts": 0,
                            "initial_connection_done": False,
                            "tracking_enabled": cam.get("tracking_enabled", False),
                            "audio_volume": cam.get("audio_volume", 30),
                        }
                        self.cameras.append(cam_obj)

                self.current_camera_index = min(
                    config.get("current_camera_index", 0), max(0, len(self.cameras) - 1)
                )

                print("Конфигурация зареDayа успешно")
            else:
                print("Конфигурационен файл не съществува")
                self.cameras = []
                self.current_camera_index = -1
        except Exception as e:
            print(f"Грешка при зареждане на конфигурация: {e}")
            traceback.print_exc()

    def initial_connection_attempts(self):
        """Първоначални последователни опити за свързване с GStreamer"""
        print("Стартиране на първоначални опити за свързване...")
        for i, camera in enumerate(self.cameras):
            print(f"Опит за свързване към камера {camera['name']} ({camera['ip']})")
            camera["last_connection_attempt"] = time.time()
            camera["connection_attempts"] = 0
            self.attempt_connection(i)

            # Ако първият опит е неуспешен, прави втори опит
            if not (camera.get("cap") and camera["cap"].isOpened()):
                print(
                    f"Първият опит за {camera['name']} е неуспешен, прави се втори опит..."
                )
                time.sleep(0.3)  # Кратко изчакване преди втори опит
                self.attempt_connection(i)

            camera["initial_connection_done"] = True
            print(f"Първоначални опити за {camera['name']} завършени")

        # Важно: Програмата трябва да продължи, дори и без връзка с устройства
        if len(self.cameras) > 0:
            # Ако има камери, но никоя не е свързана, задай първата като текуща
            self.current_camera_index = 0
            print("Инициализация завършена, дори и без активни връзки")
        else:
            print("Няма конфигурирани камери")

    def attempt_connection(self, camera_index):
        if camera_index < 0 or camera_index >= len(self.cameras):
            return

        camera = self.cameras[camera_index]

        try:
            sock = socket.create_connection((camera["ip"], 554), timeout=2)

            sock.close()

            camera["connected"] = True

        except Exception:
            camera["connected"] = False

        camera["last_connection_attempt"] = time.time()
        camera["connection_attempts"] += 1

    def save_config(self):
        try:
            cameras_data = []
            for cam in self.cameras:
                cam_data = {
                    "ip": cam["ip"],
                    "name": cam["name"],
                    "rtsp_url": cam["rtsp_url"],
                    "audio_url": cam["audio_url"],
                    "white_light_status": cam["white_light_status"],
                    "ir_light_status": cam["ir_light_status"],
                    "day_night_status": cam["day_night_status"],
                    "last_connection_attempt": 0,
                    "connection_attempts": 0,
                    "initial_connection_done": False,
                    "tracking_enabled": cam.get("tracking_enabled", False),
                    "audio_volume": cam.get("audio_volume", 100),
                }
                cameras_data.append(cam_data)

            config = {
                "movement_blocking_enabled": self.movement_blocking_enabled,
                "audio_volume": self.audio_volume,
                "cameras": cameras_data,
                "current_camera_index": self.current_camera_index,
            }
            with open(self.config_file, "w") as f:
                json.dump(config, f, indent=4)
            print("Конфигурация запазена успешно")
            self.set_status("Настройки запазени")
        except Exception as e:
            print(f"Грешка при запазване на конфигурация: {e}")
            traceback.print_exc()
            self.set_status("Грешка при запазване")

    def set_status(self, message):
        self.status_message = message
        self.status_timer = time.time()

    def draw_rounded_rect(self, surface, rect, color, radius=10):
        if surface is None:
            return
        try:
            x, y, w, h = rect
            pygame.draw.rect(surface, color, (x + radius, y, w - 2 * radius, h))
            pygame.draw.rect(surface, color, (x, y + radius, w, h - 2 * radius))
            gfxdraw.filled_circle(surface, x + radius, y + radius, radius, color)
            gfxdraw.filled_circle(surface, x + w - radius, y + radius, radius, color)
            gfxdraw.filled_circle(surface, x + radius, y + h - radius, radius, color)
            gfxdraw.filled_circle(
                surface, x + w - radius, y + h - radius, radius, color
            )
            gfxdraw.aacircle(surface, x + radius, y + radius, radius, color)
            gfxdraw.aacircle(surface, x + w - radius, y + radius, radius, color)
            gfxdraw.aacircle(surface, x + radius, y + h - radius, radius, color)
            gfxdraw.aacircle(surface, x + w - radius, y + h - radius, radius, color)
        except Exception as e:
            print("draw_rounded_rect:", e)

    def draw_button(
        self,
        surface,
        x,
        y,
        width,
        height,
        text,
        color,
        hover_color,
        font,
        action=None,
        button_id=None,
        disabled=False,
        is_toggle=False,
    ):
        if surface is None:
            return pygame.Rect(0, 0, 0, 0)
        try:
            mouse_pos = pygame.mouse.get_pos()
            mouse_click = pygame.mouse.get_pressed()
            rect = pygame.Rect(x, y, width, height)
            is_hovered = rect.collidepoint(mouse_pos) and not disabled

            is_pressed = (
                button_id
                and not is_toggle
                and self.pressed_buttons.get(button_id, False)
                and not disabled
            )

            if button_id in self.button_cooldowns:
                if time.time() - self.button_cooldowns[button_id] < 1.0:
                    disabled = True

            if disabled:
                button_color = (color[0] // 2, color[1] // 2, color[2] // 2)
            elif is_pressed:
                button_color = tuple(255 - c for c in color[:3])
            elif is_hovered:
                button_color = hover_color
            else:
                button_color = color

            self.draw_rounded_rect(surface, (x, y, width, height), button_color)
            text_surface = font.render(text, True, self.colors["text"])
            text_rect = text_surface.get_rect(center=(x + width // 2, y + height // 2))
            surface.blit(text_surface, text_rect)

            if is_hovered and mouse_click[0] and action and button_id and not disabled:
                if not self.pressed_buttons.get(button_id, False):
                    if button_id in self.button_cooldowns:
                        if time.time() - self.button_cooldowns[button_id] < 1.0:
                            return rect
                    if is_toggle:
                        action()
                        self.button_cooldowns[button_id] = time.time()
                    else:
                        self.pressed_buttons[button_id] = True
                        self.button_press_times[button_id] = time.time()
                        self.start_button_thread(button_id, action)
            return rect
        except Exception as e:
            return pygame.Rect(0, 0, 0, 0)

    def start_button_thread(self, button_id, action):
        def button_thread():
            start_time = time.time()
            while (
                self.pressed_buttons.get(button_id, False)
                and self.running
                and not self.stop_all_movements_flag
            ):
                current_time = time.time()
                press_duration = current_time - self.button_press_times.get(
                    button_id, start_time
                )
                try:
                    action()
                except Exception as e:
                    print("button action error:", e)
                if press_duration < 0.1:
                    time.sleep(0.02)
                elif press_duration < 0.5:
                    time.sleep(0.03)
                else:
                    time.sleep(0.05)
            self.pressed_buttons[button_id] = False

        thread = threading.Thread(target=button_thread, daemon=True)
        thread.start()
        self.button_threads[button_id] = thread

    def release_button(self, button_id):
        self.pressed_buttons[button_id] = False
        self.button_cooldowns[button_id] = time.time()
        self.send_stop_command()

    def release_all_buttons(self):
        for bid in list(self.pressed_buttons.keys()):
            self.pressed_buttons[bid] = False
            self.button_cooldowns[bid] = time.time()
        self.send_stop_command()

    def draw_slider(
        self,
        surface,
        x,
        y,
        width,
        height,
        value,
        min_val,
        max_val,
        label,
        is_zoom_slider=True,
        callback=None,
    ):
        if surface is None:
            return pygame.Rect(0, 0, 0, 0)
        try:
            mouse_pos = pygame.mouse.get_pos()
            mouse_click = pygame.mouse.get_pressed()
            pygame.draw.rect(
                surface, self.colors["panel"], (x, y, width, height), border_radius=5
            )
            pygame.draw.rect(
                surface,
                self.colors["border"],
                (x + 5, y + height // 2 - 2, width - 10, 4),
                border_radius=2,
            )
            fill_width = int(
                (value - min_val) / max(1e-6, (max_val - min_val)) * (width - 10)
            )
            pygame.draw.rect(
                surface,
                self.colors["accent"],
                (x + 5, y + height // 2 - 2, fill_width, 4),
                border_radius=2,
            )
            handle_x = x + 5 + fill_width
            handle_rect = pygame.Rect(handle_x - 8, y + height // 2 - 8, 16, 16)
            handle_color = (
                self.colors["accent_hover"]
                if handle_rect.collidepoint(mouse_pos)
                else self.colors["accent"]
            )
            pygame.draw.circle(surface, handle_color, (handle_x, y + height // 2), 8)
            pygame.draw.circle(
                surface, self.colors["text"], (handle_x, y + height // 2), 8, 2
            )
            label_surface = self.font_small.render(
                f"{label}: {value:.2f}"
                if not is_zoom_slider
                else f"{label}: {value:.2f}x",
                True,
                self.colors["text_secondary"],
            )
            surface.blit(label_surface, (x, y - 20))

            slider_rect = pygame.Rect(x, y, width, height)

            if (
                slider_rect.collidepoint(mouse_pos)
                and mouse_click[0]
                and "slider_zoom" not in self.button_cooldowns
                and is_zoom_slider
            ):
                self.button_cooldowns["slider_zoom"] = time.time() + 0.1
                relative_x = max(0, min(mouse_pos[0] - x, width))
                new_value = min_val + (relative_x / width) * (max_val - min_val)
                if abs(new_value - self.current_zoom) > self.zoom_step / 2:
                    self.current_zoom = max(min_val, min(new_value, max_val))
                    if new_value > self.current_zoom:
                        self.send_ptz_command("9")
                    else:
                        self.send_ptz_command("a")
                    self.set_status(f"{label}: {new_value:.2f}")

            if (
                slider_rect.collidepoint(mouse_pos)
                and mouse_click[0]
                and not is_zoom_slider
                and callback
            ):
                relative_x = max(0, min(mouse_pos[0] - x, width))
                new_value = min_val + (relative_x / width) * (max_val - min_val)
                callback(new_value)

            return slider_rect
        except Exception as e:
            print("draw_slider:", e)
            return pygame.Rect(0, 0, 0, 0)

    def draw_status_bar(self, surface):
        if surface is None:
            return
        try:
            bar_height = 20
            pygame.draw.rect(
                surface,
                self.colors["panel"],
                (0, self.screen_height - bar_height, self.screen_width, bar_height),
            )
            pygame.draw.line(
                surface,
                self.colors["border"],
                (0, self.screen_height - bar_height),
                (self.screen_width, self.screen_height - bar_height),
                2,
            )
            status_surface = self.font_small.render(
                self.status_message, True, self.colors["text"]
            )
            surface.blit(status_surface, (10, self.screen_height - bar_height + 8))

            if (
                self.cameras
                and self.current_camera_index >= 0
                and self.current_camera_index < len(self.cameras)
            ):
                coords_text = f"Zoom: {self.current_zoom:.1f}x"
                coords_surface = self.font_small.render(
                    coords_text, True, self.colors["text_secondary"]
                )
                surface.blit(
                    coords_surface,
                    (
                        self.screen_width - coords_surface.get_width() - 10,
                        self.screen_height - bar_height + 8,
                    ),
                )
        except Exception as e:
            print("draw_status_bar:", e)

    def draw_joystick(self, surface, x, y, radius):
        if surface is None:
            return {}
        try:
            pygame.draw.circle(surface, self.colors["panel"], (x, y), radius)
            pygame.draw.circle(surface, self.colors["border"], (x, y), radius, 2)
            inner_radius = radius - 10
            pygame.draw.circle(surface, self.colors["background"], (x, y), inner_radius)

            button_radius = 20
            button_spacing = 35

            up_rect = pygame.Rect(
                x - button_radius,
                y - button_spacing - button_radius,
                button_radius * 2,
                button_radius * 2,
            )
            is_pressed_up = self.pressed_buttons.get("3", False)
            up_color = (
                self.colors["accent_hover"] if is_pressed_up else self.colors["accent"]
            )
            pygame.draw.circle(
                surface, up_color, (x, y - button_spacing), button_radius
            )
            pygame.draw.polygon(
                surface,
                self.colors["text"],
                [
                    (x, y - button_spacing - 10),
                    (x - 8, y - button_spacing + 10),
                    (x + 8, y - button_spacing + 10),
                ],
            )

            down_rect = pygame.Rect(
                x - button_radius,
                y + button_spacing - button_radius,
                button_radius * 2,
                button_radius * 2,
            )
            is_pressed_down = self.pressed_buttons.get("4", False)
            down_color = (
                self.colors["accent_hover"]
                if is_pressed_down
                else self.colors["accent"]
            )
            pygame.draw.circle(
                surface, down_color, (x, y + button_spacing), button_radius
            )
            pygame.draw.polygon(
                surface,
                self.colors["text"],
                [
                    (x, y + button_spacing + 10),
                    (x - 8, y + button_spacing - 10),
                    (x + 8, y + button_spacing - 10),
                ],
            )

            left_rect = pygame.Rect(
                x - button_spacing - button_radius,
                y - button_radius,
                button_radius * 2,
                button_radius * 2,
            )
            is_pressed_left = self.pressed_buttons.get("1", False)
            left_color = (
                self.colors["accent_hover"]
                if is_pressed_left
                else self.colors["accent"]
            )
            pygame.draw.circle(
                surface, left_color, (x - button_spacing, y), button_radius
            )
            pygame.draw.polygon(
                surface,
                self.colors["text"],
                [
                    (x - button_spacing - 10, y),
                    (x - button_spacing + 10, y - 8),
                    (x - button_spacing + 10, y + 8),
                ],
            )

            right_rect = pygame.Rect(
                x + button_spacing - button_radius,
                y - button_radius,
                button_radius * 2,
                button_radius * 2,
            )
            is_pressed_right = self.pressed_buttons.get("2", False)
            right_color = (
                self.colors["accent_hover"]
                if is_pressed_right
                else self.colors["accent"]
            )
            pygame.draw.circle(
                surface, right_color, (x + button_spacing, y), button_radius
            )
            pygame.draw.polygon(
                surface,
                self.colors["text"],
                [
                    (x + button_spacing + 10, y),
                    (x + button_spacing - 10, y - 8),
                    (x + button_spacing - 10, y + 8),
                ],
            )

            center_rect = pygame.Rect(
                x - button_radius,
                y - button_radius,
                button_radius * 2,
                button_radius * 2,
            )
            pygame.draw.circle(surface, self.colors["warning"], (x, y), button_radius)
            pygame.draw.circle(surface, self.colors["text"], (x, y), 5)

            return {
                "up": up_rect,
                "down": down_rect,
                "left": left_rect,
                "right": right_rect,
                "center": center_rect,
            }
        except Exception as e:
            print("draw_joystick:", e)
            return {}

    def draw_fullscreen_controls(self, surface):
        if surface is None:
            return
        try:
            control_width = 150
            control_height = 200
            x = surface.get_width() - control_width - 20
            y = surface.get_height() - control_height - 20

            self.draw_rounded_rect(
                surface, (x, y, control_width, control_height), (20, 20, 20)
            )
            pygame.draw.rect(
                surface,
                self.colors["border"],
                (x, y, control_width, control_height),
                2,
                border_radius=10,
            )

            # Използваме joystick функцията за рисуване на контролите
            joystick_rects = self.draw_joystick(
                surface, x + control_width // 2, y + control_height // 2 - 20, 50
            )

            # Добавяме бутон за изход от Full Screen
            exit_rect = pygame.Rect(x + 10, y + control_height - 40, 30, 30)
            pygame.draw.rect(surface, self.colors["danger"], exit_rect, border_radius=5)
            exit_text = self.font_medium.render("⌫", True, self.colors["text"])
            surface.blit(exit_text, (x + 15, y + control_height - 35))

            # Връщаме всички правоъгълници за обработка на кликване
            return {
                "exit": exit_rect,
                "up": joystick_rects["up"],
                "down": joystick_rects["down"],
                "left": joystick_rects["left"],
                "right": joystick_rects["right"],
                "center": joystick_rects["center"],
            }
        except Exception as e:
            print("draw_fullscreen_controls:", e)
            return {}

    def draw_video_coordinates(self, surface, video_x, video_y):
        if surface is None:
            return
        try:
            # Display storage information instead of coordinates
            storage_text = self.get_storage_info()
            storage_surface = self.font_small.render(
                storage_text, True, self.colors["text"]
            )
            storage_rect = storage_surface.get_rect()
            storage_rect.x = video_x + 10
            storage_rect.y = video_y + 10

            pygame.draw.rect(
                surface,
                (0, 0, 0),
                (
                    storage_rect.x - 5,
                    storage_rect.y - 2,
                    storage_rect.width + 10,
                    storage_rect.height + 4,
                ),
                border_radius=3,
            )
            pygame.draw.rect(
                surface,
                self.colors["border"],
                (
                    storage_rect.x - 5,
                    storage_rect.y - 2,
                    storage_rect.width + 10,
                    storage_rect.height + 4,
                ),
                1,
                border_radius=3,
            )
            surface.blit(storage_surface, (storage_rect.x, storage_rect.y))
        except Exception as e:
            print("draw_video_coordinates:", e)

    def draw_input_field(self, surface, x, y, width, height, text, is_active, label=""):
        try:
            if label:
                label_surface = self.font_medium.render(
                    label, True, self.colors["text"]
                )
                surface.blit(label_surface, (x, y - 20))

            rect = pygame.Rect(x, y, width, height)
            pygame.draw.rect(surface, self.colors["background"], rect, border_radius=5)
            pygame.draw.rect(surface, self.colors["border"], rect, 2, border_radius=5)

            if is_active:
                pygame.draw.rect(
                    surface, self.colors["accent"], rect, 3, border_radius=5
                )

            text_surface = self.font_medium.render(text, True, self.colors["text"])
            surface.blit(text_surface, (x + 10, y + 10))

            return rect
        except Exception as e:
            print("draw_input_field:", e)
            return pygame.Rect(0, 0, 0, 0)

    def stop_all_movements(self):
        self.stop_all_movements_flag = True
        self.release_all_buttons()
        time.sleep(0.1)
        self.stop_all_movements_flag = False
        self.set_status("Всички движения спрени")

    def get_current_camera(self):
        if self.current_camera_index < 0 or self.current_camera_index >= len(
            self.cameras
        ):
            return None
        return self.cameras[self.current_camera_index]

    def add_camera(self, ip, name):
        """Добавя нова камера към списъка с валидация на IP"""
        if not self.validate_ipv4(ip):
            self.set_status("НевалиDay IP адрес")
            return -1
        camera = {
            "ip": ip,
            "name": name,
            "connected": False,
            "rtsp_url": f"rtsp://{ip}:554/0/video0",
            "audio_url": f"rtsp://{ip}:8001/0/audio",
            "cap": None,
            "mini_cap": None,
            "video_surface": None,
            "mini_video_surface": None,
            "white_light_status": False,
            "ir_light_status": False,
            "day_night_status": True,
            "last_connection_attempt": 0,
            "connection_attempts": 0,
            "initial_connection_done": True,
            "tracking_enabled": False,
            "audio_volume": 100,
        }
        self.cameras.append(camera)
        return len(self.cameras) - 1

    def remove_camera(self, index):
        """Премахва камера от списъка"""
        if 0 <= index < len(self.cameras):
            removed_camera = self.cameras.pop(index)

            try:
                if removed_camera.get("cap"):
                    removed_camera["cap"].release()
                if removed_camera.get("mini_cap"):
                    removed_camera["mini_cap"].release()
            except Exception as e:
                print(f"Error releasing removed camera: {e}")

            if self.current_camera_index == index:
                if len(self.cameras) > 0:
                    self.current_camera_index = 0
                    self.start_video_stream_async()
                    self.start_audio_stream()
                else:
                    self.current_camera_index = -1
                    self.video_surface = None
            elif self.current_camera_index > index:
                self.current_camera_index -= 1

            self.set_status(f"Премахната камера: {removed_camera.get('name', '?')}")

    def switch_camera(self, index):
        """ПреONючва към друга камера и подновява мини видеопотоци"""
        if 0 <= index < len(self.cameras):
            cur = self.get_current_camera()
            if cur and (cur.get("cap") or cur.get("mini_cap")):
                try:
                    if cur.get("cap"):
                        cur["cap"].release()
                    if cur.get("mini_cap"):
                        cur["mini_cap"].release()
                except Exception as e:
                    print(f"Error releasing current camera: {e}")
                cur["cap"] = None
                cur["mini_cap"] = None

            self.stop_audio_stream()

            self.current_camera_index = index
            self.set_status(f"ПреONючено към: {self.cameras[index]['name']}")
            self.start_video_stream_async()
            self.start_audio_stream()

            # === ПОДНОВЯВАНЕ НА МИНИ ВИДЕОПОТОЦИ СЛЕД СМЯНА НА КАМЕРА ===
            self.restart_mini_streams()

    def restart_mini_streams(self):
        """Подновява всички мини видеопотоци след смяна на фокусираната камера"""
        print("Подновяване на мини видеопотоци...")

        # Спираме всички съществуващи мини потоци
        for i, camera in enumerate(self.cameras):
            if camera.get("mini_cap"):
                try:
                    camera["mini_cap"].release()
                    camera["mini_cap"] = None
                    camera["mini_video_surface"] = None
                except Exception as e:
                    print(f"Грешка при спиране на мини поток {i}: {e}")

        # Стартираме отново мини потоци за всички камери освен текущата
        for i in range(len(self.cameras)):
            if i != self.current_camera_index:
                self.start_mini_video_stream_async(i)

        # Добавяме малко забавяне за стабилизиране на потоците
        time.sleep(0.5)
        self.set_status("Мини видеопотоци подновени")

    def send_ptz_command(self, command):
        """Изпраща PTZ команда през SSH - оптимизирана версия"""

        def worker():
            try:
                cam = self.get_current_camera()
                if cam is None:
                    return
                ssh_cmd = f"ssh -o ConnectTimeout=1 -o StrictHostKeyChecking=no root@{cam['ip']} 'ptz_test {command}'"
                result = subprocess.run(
                    ssh_cmd, shell=True, capture_output=True, text=True, timeout=2.0
                )
                if result.returncode == 0:
                    self.set_status(f"PTZ команда: {command}")
                else:
                    self.set_status("Грешка при PTZ команда")
            except subprocess.TimeoutExpired:
                self.set_status("PTZ команда изтече по време")
            except Exception as e:
                print("send_ptz_command worker:", e)
                self.set_status("Грешка при PTZ команда")

        t = threading.Thread(target=worker, daemon=True)
        t.start()

    def send_stop_command(self):
        """Спира движението на камерата"""

        def worker():
            try:
                cam = self.get_current_camera()
                if cam is None:
                    return
                ssh_cmd = f"ssh -o ConnectTimeout=1 -o StrictHostKeyChecking=no root@{cam['ip']} 'ptz_test 0'"
                result = subprocess.run(
                    ssh_cmd, shell=True, capture_output=True, text=True, timeout=2.0
                )
                if result.returncode == 0:
                    self.set_status("Движението е спряно")
            except subprocess.TimeoutExpired:
                self.set_status("Спиране изтече по време")
            except Exception as e:
                print("send_stop_command worker:", e)

        t = threading.Thread(target=worker, daemon=True)
        t.start()

    def send_diagonal_command(self, cmd1, cmd2):
        """Изпраща диагонална команда - оптимизирана версия"""

        def worker():
            try:
                cam = self.get_current_camera()
                if cam is None:
                    return
                ssh_cmd = f"ssh -o ConnectTimeout=1 -o StrictHostKeyChecking=no root@{cam['ip']} 'ptz_test {cmd1} && ptz_test {cmd2}'"
                result = subprocess.run(
                    ssh_cmd, shell=True, capture_output=True, text=True, timeout=2.0
                )
                if result.returncode == 0:
                    self.set_status(f"Диагонал: {cmd1}, {cmd2}")
            except subprocess.TimeoutExpired:
                self.set_status("Диагонална команда изтече по време")
            except Exception as e:
                print("send_diagonal_command worker:", e)
                self.set_status("Грешка при диагонална команда")

        t = threading.Thread(target=worker, daemon=True)
        t.start()

    def start_white_light_off_timer(self, delay_seconds=60):
        """Starts a timer to turn off white lights after a delay"""
        self.white_light_off_timer = time.time() + delay_seconds

    def render_ui(self):
        try:
            self.screen.fill(self.colors["background"])
            panel_width = 250

            video_width = self.screen_width - 2 * panel_width - 40
            video_height = self.screen_height - 50

            left_panel = self.draw_control_panel(
                self.screen, 10, 50, panel_width, video_height, "Control"
            )
            right_panel = self.draw_control_panel(
                self.screen,
                self.screen_width - panel_width - 10,
                50,
                panel_width,
                video_height,
                ".",
            )

            self.video_rect = pygame.Rect(
                panel_width + 20, 50, video_width, video_height
            )
            pygame.draw.rect(self.screen, (0, 0, 0), self.video_rect)
            pygame.draw.rect(self.screen, self.colors["border"], self.video_rect, 2)
            title_surface = self.font_medium.render(
                "Video Stream", True, self.colors["text"]
            )
            self.screen.blit(
                title_surface, (self.video_rect.x + 10, self.video_rect.y - 25)
            )

            self.mini_camera_rects = {}

            if self.video_surface and not self.fullscreen_mode:
                try:
                    self.screen.blit(
                        self.video_surface, (self.video_offset_x, self.video_offset_y)
                    )
                except Exception as e:
                    print("Blit video_surface error:", e)

                # Draw IP address in bottom left corner
                current_cam = self.get_current_camera()
                if current_cam:
                    ip_text = f"IP: {current_cam['ip']}"
                    ip_surface = self.font_bold.render(
                        ip_text, True, (255, 165, 0)
                    )  # Orange
                    ip_bg = pygame.Surface(
                        (ip_surface.get_width() + 10, ip_surface.get_height() + 6)
                    )
                    ip_bg.fill((0, 0, 0))  # Black background
                    self.screen.blit(
                        ip_bg,
                        (
                            self.video_offset_x + 5,
                            self.video_offset_y
                            + self.video_surface_height
                            - ip_surface.get_height()
                            - 5,
                        ),
                    )
                    self.screen.blit(
                        ip_surface,
                        (
                            self.video_offset_x + 10,
                            self.video_offset_y
                            + self.video_surface_height
                            - ip_surface.get_height()
                            - 2,
                        ),
                    )

                # Draw camera name in bottom right corner
                if current_cam:
                    name_text = f"NAME: {current_cam['name']}"
                    name_surface = self.font_bold.render(
                        name_text, True, (124, 252, 0)
                    )  # Light green
                    name_bg = pygame.Surface(
                        (name_surface.get_width() + 10, name_surface.get_height() + 6)
                    )
                    name_bg.fill((0, 0, 0))  # Black background
                    self.screen.blit(
                        name_bg,
                        (
                            self.video_offset_x
                            + self.video_surface_width
                            - name_surface.get_width()
                            - 5,
                            self.video_offset_y
                            + self.video_surface_height
                            - name_surface.get_height()
                            - 5,
                        ),
                    )
                    self.screen.blit(
                        name_surface,
                        (
                            self.video_offset_x
                            + self.video_surface_width
                            - name_surface.get_width()
                            - 5,
                            self.video_offset_y
                            + self.video_surface_height
                            - name_surface.get_height()
                            - 5,
                        ),
                    )
                # Draw PTZ X/Y coordinates in bottom right corner
                ptz_text = self.get_ptz_info()

                ptz_surface = self.font_bold.render(
                    ptz_text,
                    True,
                    (0, 255, 255),  # Cyan
                )

                ptz_bg = pygame.Surface(
                    (
                        ptz_surface.get_width() + 10,
                        ptz_surface.get_height() + 6,
                    )
                )

                ptz_bg.fill((0, 0, 0))

                # Position ABOVE camera name
                ptz_x_pos = (
                    self.video_offset_x
                    + self.video_surface_width
                    - ptz_surface.get_width()
                    - 10
                )

                ptz_y_pos = (
                    self.video_offset_y
                    + self.video_surface_height
                    - ptz_surface.get_height()
                    - 35
                )

                self.screen.blit(
                    ptz_bg,
                    (ptz_x_pos - 5, ptz_y_pos - 3),
                )

                self.screen.blit(
                    ptz_surface,
                    (ptz_x_pos, ptz_y_pos),
                )
                self.draw_video_coordinates(
                    self.screen, self.video_offset_x, self.video_offset_y
                )

            # Рисуваме само мини камерите във видеополето
            self.draw_mini_cameras(panel_width + 20, 50, video_width, video_height)

            # === Ляв панел: контроли ===
            button_height = 35
            button_spacing = 8
            start_y = 80

            # Intercom бутон (най-горе)
            self.draw_walkie_talkie_button(
                self.screen, 20, start_y, panel_width - 20, button_height
            )

            # Detection
            self.draw_button(
                self.screen,
                20,
                start_y + button_height + button_spacing,
                panel_width - 20,
                button_height,
                f"Detection: {'ON' if self.get_current_camera() and self.get_current_camera().get('tracking_enabled', False) else 'OFF'}",
                self.colors["success"]
                if self.get_current_camera()
                and self.get_current_camera().get("tracking_enabled", False)
                else self.colors["danger"],
                self.colors["accent_hover"],
                self.font_medium,
                self.toggle_object_detection,
                "toggle_object_detection",
                is_toggle=True,
            )

            # White Light
            self.draw_button(
                self.screen,
                20,
                start_y + 2 * (button_height + button_spacing),
                panel_width - 20,
                button_height,
                f"White Light: {'ON' if self.get_current_camera() and self.get_current_camera().get('white_light_status', False) else 'OFF'}",
                self.colors["success"]
                if self.get_current_camera()
                and self.get_current_camera().get("white_light_status", False)
                else self.colors["danger"],
                self.colors["accent_hover"],
                self.font_medium,
                self.toggle_white_light,
                "white_light",
                is_toggle=True,
            )

            # IR Light
            self.draw_button(
                self.screen,
                20,
                start_y + 3 * (button_height + button_spacing),
                panel_width - 20,
                button_height,
                f"IR Light: {'ON' if self.get_current_camera() and self.get_current_camera().get('ir_light_status', False) else 'OFF'}",
                self.colors["success"]
                if self.get_current_camera()
                and self.get_current_camera().get("ir_light_status", False)
                else self.colors["danger"],
                self.colors["accent_hover"],
                self.font_medium,
                self.toggle_ir_light,
                "ir_light",
                is_toggle=True,
            )

            # Day/Night
            self.draw_button(
                self.screen,
                20,
                start_y + 4 * (button_height + button_spacing),
                panel_width - 20,
                button_height,
                f"MODE: {'Day' if self.get_current_camera() and self.get_current_camera().get('day_night_status', True) else 'Night'}",
                self.colors["success"]
                if self.get_current_camera()
                and self.get_current_camera().get("day_night_status", True)
                else self.colors["danger"],
                self.colors["accent_hover"],
                self.font_medium,
                self.toggle_day_night,
                "day_night",
                is_toggle=True,
            )

            # PTZ контроли
            ptz_y = start_y + 5 * (button_height + button_spacing) + 10
            button_size = 40
            spacing = 5

            self.draw_button(
                self.screen,
                40,
                ptz_y,
                button_size,
                button_size,
                "↖",
                self.colors["accent"],
                self.colors["accent_hover"],
                self.font_large,
                lambda: self.send_diagonal_command("5"),
                "5",
            )
            self.draw_button(
                self.screen,
                90,
                ptz_y,
                button_size,
                button_size,
                "↑",
                self.colors["accent"],
                self.colors["accent_hover"],
                self.font_large,
                lambda: self.send_ptz_command("3"),
                "3",
            )
            self.draw_button(
                self.screen,
                140,
                ptz_y,
                button_size,
                button_size,
                "↗",
                self.colors["accent"],
                self.colors["accent_hover"],
                self.font_large,
                lambda: self.send_diagonal_command("6"),
                "6",
            )
            self.draw_button(
                self.screen,
                40,
                ptz_y + button_size + spacing,
                button_size,
                button_size,
                "←",
                self.colors["accent"],
                self.colors["accent_hover"],
                self.font_large,
                lambda: self.send_ptz_command("1"),
                "1",
            )
            self.draw_button(
                self.screen,
                90,
                ptz_y + button_size + spacing,
                button_size,
                button_size,
                "●",
                self.colors["warning"],
                self.colors["accent_hover"],
                self.font_large,
                lambda: self.send_ptz_command("0"),
                "0",
            )
            self.draw_button(
                self.screen,
                140,
                ptz_y + button_size + spacing,
                button_size,
                button_size,
                "→",
                self.colors["accent"],
                self.colors["accent_hover"],
                self.font_large,
                lambda: self.send_ptz_command("2"),
                "2",
            )
            self.draw_button(
                self.screen,
                40,
                ptz_y + 2 * (button_size + spacing),
                button_size,
                button_size,
                "↙",
                self.colors["accent"],
                self.colors["accent_hover"],
                self.font_large,
                lambda: self.send_diagonal_command("7"),
                "7",
            )
            self.draw_button(
                self.screen,
                90,
                ptz_y + 2 * (button_size + spacing),
                button_size,
                button_size,
                "↓",
                self.colors["accent"],
                self.colors["accent_hover"],
                self.font_large,
                lambda: self.send_ptz_command("4"),
                "4",
            )
            self.draw_button(
                self.screen,
                140,
                ptz_y + 2 * (button_size + spacing),
                button_size,
                button_size,
                "↘",
                self.colors["accent"],
                self.colors["accent_hover"],
                self.font_large,
                lambda: self.send_diagonal_command("8"),
                "8",
            )

            # Motion Tracking на движенията
            # block_y = ptz_y + 3 * (button_size + spacing) + 10
            # self.draw_button(
            #    self.screen,
            #    20,
            #    block_y,
            #    panel_width - 20,
            #    button_height,
            #    f"Motion Tracking: {'ON' if self.movement_blocking_enabled else 'OFF'}",
            #    self.colors["success"]
            #    if self.movement_blocking_enabled
            #    else self.colors["danger"],
            #    self.colors["accent_hover"],
            #    self.font_medium,
            #    self.toggle_movement_blocking,
            #    "movement_blocking",
            #    is_toggle=True,
            # )

            # Слайдери за gain
            gain_y = ptz_y + 3 * (button_size + spacing) + 40
            self.draw_slider(
                self.screen,
                20,
                gain_y,
                panel_width - 20,
                max(15, button_height // 2),
                self.mic_gain,
                0,
                100,
                "MIC GAIN (%)",
                is_zoom_slider=False,
                callback=lambda v: setattr(self, "mic_gain", int(v)),
            )
            self.draw_slider(
                self.screen,
                20,
                gain_y + max(20, button_height // 2) + 5,
                panel_width - 20,
                max(15, button_height // 2),
                self.playback_gain,
                0,
                100,
                "SOUND GAIN (%)",
                is_zoom_slider=False,
                callback=lambda v: setattr(self, "playback_gain", int(v)),
            )

            # Дефинираме recordings_y — 50 пиксела под gain слайдерите
            recordings_y = gain_y + button_height + 50

            # В render_ui, след дефинирането на recordings_y:
            self.draw_button(
                self.screen,
                20,
                recordings_y,
                panel_width - 20,
                button_height,
                "VIEW RECORDS",
                (139, 69, 19),  # Светло кафяв
                self.colors["accent_hover"],
                self.font_medium,
                self.show_recordings_window,  # Сега стартира нов прозорец
                "show_recordings",
            )

            audio_y = recordings_y + button_height + 40

            self.draw_button(
                self.screen,
                20,
                audio_y,
                panel_width - 20,
                button_height,
                "ALARM",
                self.colors["danger"],
                self.colors["accent_hover"],
                self.font_medium,
                lambda: self.play_alarm(),
                "alarm",
            )

            # === Десен панел: добавяне на камера, списък, Zoom, IR команди ===
            right_start_y = 80
            title_surface = self.font_large.render(".", True, self.colors["text"])
            self.screen.blit(
                title_surface, (self.screen_width - panel_width + 30, right_start_y)
            )

            ip_field_y = right_start_y + 30
            ip_rect = self.draw_input_field(
                self.screen,
                self.screen_width - panel_width + 10,
                ip_field_y,
                panel_width - 30,
                35,
                self.ip_input,
                self.input_active == "ip",
                "IP адрес:",
            )

            name_field_y = ip_field_y + 60
            name_rect = self.draw_input_field(
                self.screen,
                self.screen_width - panel_width + 10,
                name_field_y,
                panel_width - 30,
                35,
                self.name_input,
                self.input_active == "name",
                "Name:",
            )

            btn_y = name_field_y + 50
            self.draw_button(
                self.screen,
                self.screen_width - panel_width + 10,
                btn_y,
                (panel_width - 40) // 2,
                35,
                "Add",
                self.colors["success"],
                self.colors["accent_hover"],
                self.font_medium,
                self.add_new_camera_from_input,
                "add_new_camera",
            )
            self.draw_button(
                self.screen,
                self.screen_width - panel_width + 10 + (panel_width - 40) // 2 + 10,
                btn_y,
                (panel_width - 40) // 2,
                35,
                "SAVE",
                self.colors["accent"],
                self.colors["accent_hover"],
                self.font_medium,
                self.save_config,
                "save",
            )

            # Camera List
            cam_list_y = btn_y + 50
            cam_list_title = self.font_large.render(
                "Camera List", True, self.colors["text"]
            )
            self.screen.blit(
                cam_list_title, (self.screen_width - panel_width + 10, cam_list_y)
            )

            for i, camera in enumerate(self.cameras):
                cam_btn_y = cam_list_y + 40 + i * (button_height + 5)
                btn_text = (
                    f"{camera['name'][:15]}..."
                    if len(camera["name"]) > 15
                    else camera["name"]
                )
                if i == self.current_camera_index:
                    btn_text = f"[{btn_text}]"
                self.draw_button(
                    self.screen,
                    self.screen_width - panel_width + 10,
                    cam_btn_y,
                    panel_width - 30,
                    button_height,
                    btn_text,
                    self.colors["success"]
                    if i == self.current_camera_index
                    else self.colors["accent"],
                    self.colors["accent_hover"],
                    self.font_small,
                    lambda idx=i: self.switch_camera(idx),
                    f"camera_{id}",
                    is_toggle=True,
                )
                if len(self.cameras) > 1:
                    self.draw_button(
                        self.screen,
                        self.screen_width - panel_width + 10 + (panel_width - 30) - 30,
                        cam_btn_y + 5,
                        25,
                        25,
                        "X",
                        self.colors["danger"],
                        self.colors["accent_hover"],
                        self.font_small,
                        lambda idx=i: self.remove_camera(idx),
                        f"remove_camera_{id}",
                    )

            # Zoom
            zoom_y = cam_list_y + 60 + len(self.cameras) * (button_height + 5)
            current_cam = self.get_current_camera()
            if current_cam:
                cam_zoom = current_cam.get("current_zoom", 1.0)
                self.draw_slider(
                    self.screen,
                    self.screen_width - panel_width + 10,
                    zoom_y,
                    panel_width - 30,
                    20,
                    cam_zoom,
                    1.0,
                    self.max_zoom,
                    "Zoom",
                    is_zoom_slider=True,
                )

                self.draw_button(
                    self.screen,
                    self.screen_width - panel_width + 10,
                    zoom_y + 30,
                    (panel_width - 35) // 2,
                    button_height,
                    "Zoom +",
                    self.colors["accent"],
                    self.colors["accent_hover"],
                    self.font_medium,
                    lambda: self.send_ptZ_command("9"),  # zoom-in
                    "zoom_in",
                )
                self.draw_button(
                    self.screen,
                    self.screen_width - panel_width + 10 + (panel_width - 35) // 2 + 5,
                    zoom_y + 30,
                    (panel_width - 35) // 2,
                    button_height,
                    "Zoom -",
                    self.colors["accent"],
                    self.colors["accent_hover"],
                    self.font_medium,
                    lambda: self.send_ptz_command("a"),  # zoom-out
                    "zoom_out",
                )

                self.draw_button(
                    self.screen,
                    self.screen_width - panel_width + 10,
                    zoom_y + 70,
                    panel_width - 30,
                    button_height,
                    "Reset Zoom",
                    self.colors["accent"],
                    self.colors["accent_hover"],
                    self.font_medium,
                    self.reset_zoom,
                    "reset_zoom",
                )

            # IR команди
            ir_y = zoom_y + 140 if current_cam else zoom_y
            ir_buttons = [
                ("IR Filter Day", lambda: self.cgi_cmd("ircut_only?mode=day")),
                ("IR Filter Night", lambda: self.cgi_cmd("ircut_only?mode=night")),
                ("IRCUT Day (color)", lambda: self.cgi_cmd("ircut?mode=day")),
                ("IRCUT Night (Ч/Б)", lambda: self.cgi_cmd("ircut?mode=night")),
                ("IR Day mode", lambda: self.cgi_cmd("irctrl?mode=day")),
                ("IR Night mode", lambda: self.cgi_cmd("irctrl?mode=night")),
            ]
            for i, (text, cmd_func) in enumerate(ir_buttons):
                self.draw_button(
                    self.screen,
                    self.screen_width - panel_width + 10,
                    ir_y + i * (button_height + 5),
                    panel_width - 30,
                    button_height,
                    text,
                    self.colors["accent"],
                    self.colors["accent_hover"],
                    self.font_small,
                    cmd_func,
                    f"ir_{i}",
                )

            sensor_y = ir_y + len(ir_buttons) * (button_height + 5) + 20
            self.draw_button(
                self.screen,
                self.screen_width - panel_width + 10,
                sensor_y,
                panel_width - 30,
                button_height,
                "Sensor IN",
                self.colors["accent"],
                self.colors["accent_hover"],
                self.font_medium,
                lambda: self.cgi_cmd("testdualsensor?mode=in"),
                "sensor_in",
            )
            self.draw_button(
                self.screen,
                self.screen_width - panel_width + 10,
                sensor_y + button_height + 5,
                panel_width - 30,
                button_height,
                "Sensor OUT",
                self.colors["accent"],
                self.colors["accent_hover"],
                self.font_medium,
                lambda: self.cgi_cmd("testdualsensor?mode=out"),
                "sensor_out",
            )

            # Горен десен ъгъл: запазване и Full Screen
            settings_y = 10
            self.draw_button(
                self.screen,
                self.screen_width - 200,
                settings_y,
                90,
                30,
                "SAVE",
                self.colors["success"],
                self.colors["accent_hover"],
                self.font_medium,
                self.save_config,
                "save",
            )
            self.draw_button(
                self.screen,
                self.screen_width - 100,
                settings_y,
                90,
                30,
                "Full Screen",
                self.colors["warning"],
                self.colors["accent_hover"],
                self.font_medium,
                self.toggle_fullscreen,
                "fullscreen",
            )

            self.draw_status_bar(self.screen)

            pygame.display.flip()
        except Exception as e:
            print("Грешка при рендиране на UI:", e)
            traceback.print_exc()

    def draw_mini_cameras(self, video_x, video_y, video_width, video_height):
        try:
            mini_camera_height = 200
            mini_camera_width = 360
            mini_camera_spacing = 10
            mini_cameras_area_y = video_y + video_height - mini_camera_height - 20

            # Винаги извеждаме всички камери освен текущата, в фиксиран ред
            other_cameras = []
            for i, cam in enumerate(self.cameras):
                if i != self.current_camera_index:
                    other_cameras.append((i, cam))

            # Сортираме по индекс за консистентност
            other_cameras.sort(key=lambda x: x[0])

            max_mini_cameras = min(len(other_cameras), 5)
            if max_mini_cameras == 0:
                return

            total_width = (
                max_mini_cameras * mini_camera_width
                + (max_mini_cameras - 1) * mini_camera_spacing
            )

            start_x = video_x + (video_width - total_width) // 2

            for i in range(max_mini_cameras):
                if i >= len(other_cameras):
                    break

                camera_index, camera = other_cameras[i]

                mini_x = start_x + i * (mini_camera_width + mini_camera_spacing)
                mini_y = mini_cameras_area_y

                mini_rect = pygame.Rect(
                    mini_x, mini_y, mini_camera_width, mini_camera_height
                )
                self.mini_camera_rects[camera_index] = mini_rect

                # Проверяваме дали камерата е активна
                is_connected = (
                    camera.get("mini_cap") and camera["mini_cap"].isOpened()
                ) or (camera.get("cap") and camera["cap"].isOpened())

                border_color = (
                    self.colors["accent"]
                    if camera_index == self.current_camera_index
                    else self.colors["border"]
                )
                pygame.draw.rect(
                    self.screen, border_color, mini_rect, 2, border_radius=5
                )

                # Рисуваме видео от камерата в мини прозореца
                if camera.get("mini_video_surface") and is_connected:
                    try:
                        scaled_surface = pygame.transform.scale(
                            camera["mini_video_surface"],
                            (mini_camera_width - 4, mini_camera_height - 4),
                        )
                        self.screen.blit(scaled_surface, (mini_x + 2, mini_y + 2))
                    except Exception as e:
                        print(f"Error scaling mini camera {i}: {e}")
                else:
                    # Ако няма видео, показваме състояние
                    status_text = "ONLINE" if is_connected else "OFFLINE"
                    status_color = (
                        self.colors["success"]
                        if is_connected
                        else self.colors["danger"]
                    )
                    status_surface = self.font_small.render(
                        status_text, True, status_color
                    )
                    status_x = (
                        mini_x + (mini_camera_width - status_surface.get_width()) // 2
                    )
                    status_y = (
                        mini_y + (mini_camera_height - status_surface.get_height()) // 2
                    )
                    self.screen.blit(status_surface, (status_x, status_y))

                    # Draw spinning circle animation if attempting connection
                    conn_state = self.camera_connectivity_states.get(camera_index)
                    if conn_state and conn_state.get("attempting", False):
                        # Calculate rotation angle based on time since attempt started
                        elapsed = time.time() - conn_state.get(
                            "start_time", time.time()
                        )
                        angle = (elapsed * 5) % 360  # Rotate 5 degrees per second

                        # Draw spinning circle
                        center_x = mini_x + mini_camera_width // 2
                        center_y = mini_y + mini_camera_height // 2
                        radius = 15
                        end_x = center_x + radius * np.cos(np.radians(angle))
                        end_y = center_y + radius * np.sin(np.radians(angle))

                        pygame.draw.line(
                            self.screen,
                            self.colors["accent"],
                            (center_x, center_y),
                            (end_x, end_y),
                            3,
                        )

                # Draw camera name with red color and bold font on black background
                name_surface = self.font_bold.render(
                    camera["name"][:15],
                    True,
                    (255, 0, 0),  # Red color
                )
                name_bg = pygame.Surface(
                    (name_surface.get_width() + 4, name_surface.get_height() + 2)
                )
                name_bg.fill((0, 0, 0))  # Black background
                name_x = mini_x + (mini_camera_width - name_surface.get_width()) // 2
                name_y = mini_y + mini_camera_height - name_surface.get_height() - 2
                self.screen.blit(name_bg, (name_x - 2, name_y - 1))
                self.screen.blit(name_surface, (name_x, name_y))

                if camera_index == self.current_camera_index:
                    pygame.draw.rect(
                        self.screen,
                        self.colors["success"],
                        (mini_x, mini_y, 10, 10),
                        border_radius=5,
                    )

        except Exception as e:
            print(f"Error drawing mini cameras: {e}")

    def draw_fullscreen_mini_cameras(self, screen_width, screen_height):
        try:
            mini_camera_height = 200
            mini_camera_width = 200
            mini_camera_spacing = 10
            mini_cameras_area_y = screen_height - mini_camera_height - 20

            # Винаги извеждаме всички камери освен текущата, в фиксиран ред
            other_cameras = []
            for i, cam in enumerate(self.cameras):
                if i != self.current_camera_index:
                    other_cameras.append((i, cam))

            # Сортираме по индекс за консистентност
            other_cameras.sort(key=lambda x: x[0])

            max_mini_cameras = min(len(other_cameras), 5)
            if max_mini_cameras == 0:
                return

            total_width = (
                max_mini_cameras * mini_camera_width
                + (max_mini_cameras - 1) * mini_camera_spacing
            )

            start_x = (screen_width - total_width) // 2

            for i in range(max_mini_cameras):
                if i >= len(other_cameras):
                    break

                camera_index, camera = other_cameras[i]

                mini_x = start_x + i * (mini_camera_width + mini_camera_spacing)
                mini_y = mini_cameras_area_y

                mini_rect = pygame.Rect(
                    mini_x, mini_y, mini_camera_width, mini_camera_height
                )
                self.mini_camera_rects[camera_index] = mini_rect

                # Проверяваме дали камерата е активна
                is_connected = (
                    camera.get("mini_cap") and camera["mini_cap"].isOpened()
                ) or (camera.get("cap") and camera["cap"].isOpened())

                border_color = (
                    self.colors["accent"]
                    if camera_index == self.current_camera_index
                    else self.colors["border"]
                )
                pygame.draw.rect(
                    self.screen, border_color, mini_rect, 2, border_radius=5
                )

                # Рисуваме видео от камерата в мини прозореца
                if camera.get("mini_video_surface") and is_connected:
                    try:
                        scaled_surface = pygame.transform.scale(
                            camera["mini_video_surface"],
                            (mini_camera_width - 4, mini_camera_height - 4),
                        )
                        self.screen.blit(scaled_surface, (mini_x + 2, mini_y + 2))
                    except Exception as e:
                        print(f"Error scaling fullscreen mini camera {i}: {e}")
                else:
                    # Ако няма видео, показваме състояние
                    status_text = "ONLINE" if is_connected else "OFFLINE"
                    status_color = (
                        self.colors["success"]
                        if is_connected
                        else self.colors["danger"]
                    )
                    status_surface = self.font_small.render(
                        status_text, True, status_color
                    )
                    status_x = (
                        mini_x + (mini_camera_width - status_surface.get_width()) // 2
                    )
                    status_y = (
                        mini_y + (mini_camera_height - status_surface.get_height()) // 2
                    )
                    self.screen.blit(status_surface, (status_x, status_y))

                    # Draw spinning circle animation if attempting connection
                    conn_state = self.camera_connectivity_states.get(camera_index)
                    if conn_state and conn_state.get("attempting", False):
                        # Calculate rotation angle based on time since attempt started
                        elapsed = time.time() - conn_state.get(
                            "start_time", time.time()
                        )
                        angle = (elapsed * 5) % 360  # Rotate 5 degrees per second

                        # Draw spinning circle
                        center_x = mini_x + mini_camera_width // 2
                        center_y = mini_y + mini_camera_height // 2
                        radius = 15
                        end_x = center_x + radius * np.cos(np.radians(angle))
                        end_y = center_y + radius * np.sin(np.radians(angle))

                        pygame.draw.line(
                            self.screen,
                            self.colors["accent"],
                            (center_x, center_y),
                            (end_x, end_y),
                            3,
                        )

                # Draw camera name with red color and bold font on black background
                name_surface = self.font_bold.render(
                    camera["name"][:20],
                    True,
                    (255, 0, 0),  # Red color
                )
                name_bg = pygame.Surface(
                    (name_surface.get_width() + 4, name_surface.get_height() + 2)
                )
                name_bg.fill((0, 0, 0))  # Black background
                name_x = mini_x + (mini_camera_width - name_surface.get_width()) // 2
                name_y = mini_y + mini_camera_height - name_surface.get_height() - 2
                self.screen.blit(name_bg, (name_x - 2, name_y - 1))
                self.screen.blit(name_surface, (name_x, name_y))

                if camera_index == self.current_camera_index:
                    pygame.draw.rect(
                        self.screen,
                        self.colors["success"],
                        (mini_x, mini_y, 10, 10),
                        border_radius=5,
                    )

        except Exception as e:
            print(f"Error drawing fullscreen mini cameras: {e}")

    def draw_control_panel(self, surface, x, y, width, height, title):
        if surface is None:
            return pygame.Rect(0, 0, 0, 0)
        try:
            title_surface = self.font_large.render(title, True, self.colors["text"])
            surface.blit(title_surface, (x + 10, y - 30))
            self.draw_rounded_rect(surface, (x, y, width, height), self.colors["panel"])
            pygame.draw.rect(
                surface,
                self.colors["border"],
                (x, y, width, height),
                2,
                border_radius=10,
            )
            return pygame.Rect(x, y, width, height)
        except Exception as e:
            print("draw_control_panel:", e)
            return pygame.Rect(0, 0, 0, 0)

    def add_new_camera_from_input(self):
        """Добавя нова камера от въвеDayите данни"""
        if self.ip_input.strip():
            ip = self.ip_input.strip()
            if not self.validate_ipv4(ip):
                self.set_status("НевалиDay IP адрес")
                return
            name = (
                self.name_input.strip()
                if self.name_input.strip()
                else f"Камера {len(self.cameras) + 1}"
            )
            self.add_camera(ip, name)
            self.ip_input = ""
            self.name_input = ""
            self.input_active = None
            self.set_status("Камерата е добавена")
            self.save_config()
        else:
            self.set_status("Моля въведете IP адрес!")

    def render_fullscreen(self):
        try:
            # Ако нямаме fullscreen_surface, създаваме я
            if self.fullscreen_surface is None:
                info = pygame.display.Info()
                self.fullscreen_surface = pygame.Surface(
                    (info.current_w, info.current_h)
                )

            # Изчистваме повърхността
            self.fullscreen_surface.fill((0, 0, 0))

            # Рисуваме видео
            if self.video_surface:
                try:
                    # Изчисляваме центриране на видео
                    vid_w, vid_h = self.video_surface.get_size()
                    screen_w, screen_h = self.fullscreen_surface.get_size()

                    # Изчисляваме отместване за центриране
                    offset_x = (screen_w - vid_w) // 2
                    offset_y = (screen_h - vid_h) // 2

                    self.fullscreen_surface.blit(
                        self.video_surface, (offset_x, offset_y)
                    )
                except Exception as e:
                    print("Blit fullscreen video_surface error:", e)

                # Draw IP address in bottom left corner
                current_cam = self.get_current_camera()
                if current_cam:
                    ip_text = f"IP: {current_cam['ip']}"
                    ip_surface = self.font_bold.render(
                        ip_text, True, (255, 165, 0)
                    )  # Orange
                    ip_bg = pygame.Surface(
                        (ip_surface.get_width() + 10, ip_surface.get_height() + 6)
                    )
                    ip_bg.fill((0, 0, 0))  # Black background
                    screen_w, screen_h = self.fullscreen_surface.get_size()
                    self.fullscreen_surface.blit(
                        ip_bg,
                        (
                            5,
                            screen_h - ip_surface.get_height() - 5,
                        ),
                    )
                    self.fullscreen_surface.blit(
                        ip_surface,
                        (
                            10,
                            screen_h - ip_surface.get_height() - 2,
                        ),
                    )

                # Draw camera name in bottom right corner
                if current_cam:
                    name_text = f"NAME: {current_cam['name']}"
                    name_surface = self.font_bold.render(
                        name_text, True, (124, 252, 0)
                    )  # Light green
                    name_bg = pygame.Surface(
                        (name_surface.get_width() + 10, name_surface.get_height() + 6)
                    )
                    name_bg.fill((0, 0, 0))  # Black background
                    screen_w, screen_h = self.fullscreen_surface.get_size()
                    self.fullscreen_surface.blit(
                        name_bg,
                        (
                            screen_w - name_surface.get_width() - 5,
                            screen_h - name_surface.get_height() - 5,
                        ),
                    )
                    self.fullscreen_surface.blit(
                        name_surface,
                        (
                            screen_w - name_surface.get_width() - 10,
                            screen_h - name_surface.get_height() - 2,
                        ),
                    )

                self.draw_video_coordinates(self.fullscreen_surface, 0, 0)

            # Рисуваме мини камерите
            self.mini_camera_rects = {}
            self.draw_fullscreen_mini_cameras(
                self.fullscreen_surface.get_width(),
                self.fullscreen_surface.get_height(),
            )

            # Рисуваме контролите за Full Screen
            self.draw_fullscreen_controls(self.fullscreen_surface)

            # Копираме съдържанието на fullscreen_surface в основния екран
            self.screen.blit(self.fullscreen_surface, (0, 0))
            pygame.display.flip()
        except Exception as e:
            print("Грешка при рендиране на Full Screen:", e)
            traceback.print_exc()

    def toggle_fullscreen(self):
        try:
            self.fullscreen_mode = not self.fullscreen_mode

            if self.fullscreen_mode:
                # Запазваме текущите размери за връщане
                self.windowed_width = self.screen_width
                self.windowed_height = self.screen_height

                # ПреONючваме към Full Screen
                info = pygame.display.Info()
                self.screen = pygame.display.set_mode(
                    (info.current_w, info.current_h),
                    pygame.FULLSCREEN | pygame.DOUBLEBUF | pygame.HWSURFACE,
                )
                self.screen_width, self.screen_height = info.current_w, info.current_h
                self.set_status("mode на Full Screen: ON")

                # Създаваме fullscreen surface ако не съществува
                if self.fullscreen_surface is None:
                    self.fullscreen_surface = pygame.Surface(
                        (info.current_w, info.current_h)
                    )
            else:
                # Връщаме към нормален mode
                self.screen = pygame.display.set_mode(
                    (self.windowed_width, self.windowed_height),
                    pygame.RESIZABLE | pygame.DOUBLEBUF | pygame.HWSURFACE,
                )
                self.screen_width = self.windowed_width
                self.screen_height = self.windowed_height
                self.set_status("mode на Full Screen: OFF")

        except Exception as e:
            print("Грешка при преONючване на Full Screen:", e)
            traceback.print_exc()
            self.fullscreen_mode = False
            try:
                self.screen_width, self.screen_height = 960, 600
                self.screen = pygame.display.set_mode(
                    (self.screen_width, self.screen_height),
                    pygame.RESIZABLE | pygame.DOUBLEBUF | pygame.HWSURFACE,
                )
            except:
                pass
            self.set_status("Грешка при преONючване на Full Screen")

    def apply_zoom(
        self,
        frame,
        zoom_factor,
        displayed_video_offset_x=0,
        displayed_video_offset_y=0,
        displayed_video_width=0,
        displayed_video_height=0,
    ):
        if zoom_factor <= 1.0 or frame is None or frame.size == 0:
            return frame

        original_frame_height, original_frame_width = frame.shape[:2]

        new_width_cropped = max(1, int(original_frame_width / zoom_factor))
        new_height_cropped = max(1, int(original_frame_height / zoom_factor))

        center_x_on_frame = original_frame_width // 2
        center_y_on_frame = original_frame_height // 2

        center_x_on_frame = max(0, min(original_frame_width - 1, center_x_on_frame))
        center_y_on_frame = max(0, min(original_frame_height - 1, center_y_on_frame))

        x1 = max(0, center_x_on_frame - new_width_cropped // 2)
        y1 = max(0, center_y_on_frame - new_height_cropped // 2)

        x2 = min(original_frame_width, x1 + new_width_cropped)
        y2 = min(original_frame_height, y1 + new_height_cropped)

        if (x2 - x1) < new_width_cropped:
            x1 = max(0, x2 - new_width_cropped)
        if (y2 - y1) < new_height_cropped:
            y1 = max(0, y2 - new_height_cropped)

        actual_cropped_width = x2 - x1
        actual_cropped_height = y2 - y1

        if actual_cropped_width <= 0 or actual_cropped_height <= 0:
            return frame

        cropped = frame[y1:y2, x1:x2]

        if cropped.size > 0:
            try:
                frame = cv2.resize(
                    cropped,
                    (original_frame_width, original_frame_height),
                    interpolation=cv2.INTER_LINEAR,
                )
            except cv2.error as e:
                print(f"Грешка при оразмеряване на изрязан кадър: {e}")
                return frame
        return frame

    def zoom_in(self):
        if "zoom_in" in self.button_cooldowns:
            if time.time() - self.button_cooldowns["zoom_in"] < 0.3:
                return

        cam = self.get_current_camera()
        if cam:
            with self.position_lock:
                current_zoom = cam.get("current_zoom", 1.0)
                new_zoom = min(self.max_zoom, current_zoom + self.zoom_step)
                cam["current_zoom"] = new_zoom
            self.send_ptz_command("9")  # zoom-in
            self.set_status(f"Zoom: {new_zoom:.1f}x")
            self.button_cooldowns["zoom_in"] = time.time()

    def zoom_out(self):
        if "zoom_out" in self.button_cooldowns:
            if time.time() - self.button_cooldowns["zoom_out"] < 0.3:
                return

        cam = self.get_current_camera()
        if cam:
            with self.position_lock:
                current_zoom = cam.get("current_zoom", 1.0)
                new_zoom = max(1.0, current_zoom - self.zoom_step)
                cam["current_zoom"] = new_zoom
            self.send_ptz_command("a")  # zoom-out
            self.set_status(f"Zoom: {new_zoom:.1f}x")
            self.button_cooldowns["zoom_out"] = time.time()

    def reset_zoom(self):
        if "reset_zoom" in self.button_cooldowns:
            if time.time() - self.button_cooldowns["reset_zoom"] < 1.0:
                return

        cam = self.get_current_camera()
        if cam:
            with self.position_lock:
                cam["current_zoom"] = 1.0
            self.set_status("Zoomът е нулиран")
            self.button_cooldowns["reset_zoom"] = time.time()

    def start_video_stream_async(self):
        """Стартира видео поток асинхронно без да блокира основния поток"""

        def worker():
            self.start_video_stream_gstreamer()

        thread = threading.Thread(target=worker)
        thread.daemon = True
        thread.start()

    def start_video_stream_gstreamer(self):
        """Стартира видео поток за текущата камера с GStreamer"""
        cam = self.get_current_camera()
        if cam is None:
            return

        if cam.get("cap"):
            try:
                cam["cap"].release()
            except Exception as e:
                print(f"Error releasing previous cap: {e}")
            cam["cap"] = None

        try:
            # GStreamer pipeline за ниска латентност голям видео прозорец

            gst_pipeline = (
                f"rtspsrc location=rtsp://{cam['ip']}:554/0/video0 "
                f"protocols=tcp "
                f"latency=100 "
                f"drop-on-latency=true "
                f"timeout=5000000 "
                f"! rtpjitterbuffer drop-on-latency=true "
                f"! rtph265depay "
                f"! h265parse "
                f"! nvh265dec "
                f"! videoconvert "
                f"! video/x-raw,format=BGR "
                f"! appsink drop=true max-buffers=1 sync=false"
            )

            cap = cv2.VideoCapture(gst_pipeline, cv2.CAP_GSTREAMER)

            #            gst_pipeline = (
            #                f"rtspsrc location=rtsp://{cam['ip']}:554/0/video0 "
            #                f"protocols=tcp latency=10 drop-on-latency=true "
            #                f"! rtpjitterbuffer ! rtph265depay ! h265parse ! avdec_h265 ! videoconvert "
            #                f"! video/x-raw,format=BGR ! appsink drop=true max-buffers=1 sync=false"
            #            )
            #
            #            cap = cv2.VideoCapture(gst_pipeline, cv2.CAP_GSTREAMER)

            cam["connected"] = cap.isOpened()
            cam["cap"] = cap if cam["connected"] else None

            if cam["connected"]:
                print(f"Успешно свързване към {cam['name']} (GStreamer)")
                self.set_status(f"Свързан към: {cam['name']}")
            else:
                if cap:
                    cap.release()
                    del cap
                    gc.collect()

                time.sleep(0.2)

        except Exception as e:
            print(f"Грешка при свързване към камера: {e}")
            cam["connected"] = False
            self.set_status(f"Грешка при свързване към: {cam['name']}")
            # Осигуряване че ресурсите са освобоDayи
            if "cap" in locals() and cap:
                try:
                    cap.release()
                except:
                    pass

    def start_mini_video_stream_async(self, camera_index):
        """Стартира мини видео поток асинхронно без да блокира основния поток"""

        def worker():
            self.start_mini_video_stream_gstreamer(camera_index)

        thread = threading.Thread(target=worker)
        thread.daemon = True
        thread.start()

    def start_mini_video_stream_gstreamer(self, camera_index):
        """Стартира мини видео поток за мини камера с GStreamer"""
        if camera_index < 0 or camera_index >= len(self.cameras):
            return

        cam = self.cameras[camera_index]

        if cam.get("mini_cap"):
            try:
                cam["mini_cap"].release()
            except Exception as e:
                print(f"Error releasing previous mini cap: {e}")
            cam["mini_cap"] = None

        try:
            # GStreamer pipeline за ниска латентност

            gst_pipeline = (
                f"rtspsrc location=rtsp://{cam['ip']}:554/0/video1"
                f"protocols=tcp "
                f"latency=200 "
                f"drop-on-latency=true "
                f"timeout=5000000 "
                f"! rtpjitterbuffer drop-on-latency=true "
                f"! rtph265depay "
                f"! h265parse "
                f"! nvh265dec "
                f"! videoconvert "
                f"! video/x-raw,format=BGR "
                f"! appsink drop=true max-buffers=1 sync=false"
            )

            cap = cv2.VideoCapture(gst_pipeline, cv2.CAP_GSTREAMER)

            #            gst_pipeline = (
            #                f"rtspsrc location=rtsp://{cam['ip']}:554/0/video0 "
            #                f"protocols=tcp latency=10 drop-on-latency=true "
            #                f"! rtpjitterbuffer ! rtph265depay ! h265parse ! avdec_h265 ! videoconvert "
            #                f"! video/x-raw,format=BGR ! appsink drop=true max-buffers=1 sync=false"
            #            )
            #
            #            cap = cv2.VideoCapture(gst_pipeline, cv2.CAP_GSTREAMER)

            connected = cap.isOpened()
            if connected:
                cam["mini_cap"] = cap
                cam["connected"] = True
                self.set_status(f"Свързан към мини видео поток: {cam['name']}")
            else:
                if cap:
                    cap.release()
                    del cap
                    gc.collect()

                time.sleep(0.2)

                cam["mini_cap"] = None
                cam["connected"] = False
        except Exception as e:
            print(f"Грешка при свързване към мини камера: {e}")
            cam["mini_cap"] = None
            cam["connected"] = False
            self.set_status(f"Грешка при свързване към мини камера: {cam['name']}")

    def stop_video_stream(self):
        cam = self.get_current_camera()
        if cam is None:
            return

        try:
            if cam.get("cap"):
                cam["cap"].release()
                cam["cap"] = None
            self.set_status("Видео потокът е спрян")
        except Exception as e:
            print(f"Error releasing video cap: {e}")

    def start_audio_stream(self):
        """Стартира аудио поток от същия RTSP адрес като видеото"""
        cam = self.get_current_camera()
        if cam is None:
            return

        self.stop_audio_stream()

        try:
            if not cam.get("audio_url"):
                return

            # Използваме RTSP адрес за аудио, но и с флагове за аудио
            cmd = [
                "gst-launch-1.0",
                "-v",
                "rtspsrc",
                f"location=rtsp://{cam['ip']}:8001/0/audio",
                "protocols=udp",
                "latency=60",
                "drop-on-latency=true",
                "!",
                "rtppcmadepay",
                "!",
                "alawdec",
                "!",
                "queue",
                "max-size-buffers=1",
                "leaky=downstream",
                "!",
                "audioconvert",
                "!",
                "autoaudiosink",
                "sync=false",
            ]

            self.audio_process = subprocess.Popen(
                cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
            )
            self.audio_process_pid = self.audio_process.pid
            print(
                f"Аудио поток стартиран за {cam['name']} с PID: {self.audio_process_pid}"
            )
        except Exception as e:
            print(f"Грешка при стартиране на аудио: {e}")
            traceback.print_exc()

    def stop_audio_stream(self):
        try:
            if hasattr(self, "audio_process") and self.audio_process:
                print("Спиране на аудио потока...")
                try:
                    self.audio_process.terminate()
                    self.audio_process.wait(timeout=0.5)
                except subprocess.TimeoutExpired:
                    print("GStreamer process did not terminate, killing it...")
                    self.audio_process.kill()
                    self.audio_process.wait(timeout=1.0)
                self.audio_process = None
                self.audio_process_pid = None
                print("Аудио поток спрян")
        except Exception as e:
            print(f"stop_audio_stream error: {e}")
            try:
                if self.audio_process_pid:
                    os.kill(self.audio_process_pid, signal.SIGTERM)
                    time.sleep(0.5)
                    try:
                        os.kill(self.audio_process_pid, 0)
                        os.kill(self.audio_process_pid, signal.SIGKILL)
                        print(f"Killed audio process by PID {self.audio_process_pid}")
                    except OSError:
                        pass
            except Exception as e2:
                print(f"Further error trying to kill audio process by PID: {e2}")
            self.audio_process = None
            self.audio_process_pid = None

    def cgi_cmd(self, command):
        """Изпраща CGI команда за светлини и други функции"""

        def worker():
            try:
                cam = self.get_current_camera()
                if cam is None:
                    return

                ports = [8001, 80]  # Изпращаме към двата порта
                success = False

                for port in ports:
                    try:
                        url = (
                            f"http://{cam['ip']}:{port}/cgi-bin/webui?command={command}"
                        )
                        response = self.http_session.get(
                            url, timeout=3
                        )  # По-кратък таймаут
                        if response.status_code == 200:
                            success = True
                            self.set_status(
                                f"CGI команда изпълнена: {command} (порт {port})"
                            )
                            break  # Ако е успешно на единия порт, не продължаваме
                        else:
                            print(
                                f"Грешка CGI команда на порт {port}: {response.status_code}"
                            )
                    except requests.exceptions.ConnectionError:
                        print(f"Няма връзка към порт {port}")
                        continue
                    except Exception as e:
                        print(f"Грешка при CGI команда на порт {port}: {e}")
                        continue

                if not success:
                    self.connection_lost = True
                    self.set_status("Грешка: Неуспешно изпращане на CGI команда")

            except Exception as e:
                print(f"Обща грешка в cgi_cmd: {e}")
                self.set_status("Грешка CGI команда")

        t = threading.Thread(target=worker)
        t.daemon = True
        t.start()

    def toggle_object_detection(self):
        """ПреONючва Detection на обекти"""
        current_cam = self.get_current_camera()
        if current_cam:
            current_cam["tracking_enabled"] = not current_cam.get(
                "tracking_enabled", False
            )
            if current_cam["tracking_enabled"]:
                self.set_status("Detection на обекти е СТАРТИРАНО")
            else:
                self.set_status("Detection на обекти е СПРЯНО")
            self.save_config()

    def toggle_white_light(self):
        """ПреONючва бялата светлина ЧРЕЗ CGI КОМАНДИ"""
        # Проверка за cooldown (1 секунда)
        if "white_light" in self.button_cooldowns:
            if time.time() - self.button_cooldowns["white_light"] < 1.0:
                return

        try:
            cam = self.get_current_camera()
            if cam is None:
                return

            cam["white_light_status"] = not cam.get("white_light_status", False)
            # Използване на CGI команди вместо PTZ
            cmd = "Won" if cam["white_light_status"] else "Woff"
            self.cgi_cmd(cmd)  # Използваме CGI вместо PTZ
            self.set_status(
                f"White Light: {'ON' if cam['white_light_status'] else 'OFF'}"
            )
            # Задаване на cooldown (1 секунда)
            self.button_cooldowns["white_light"] = time.time()
        except Exception as e:
            print(f"Грешка при преONючване на бялата светлина: {e}")
            traceback.print_exc()

    def toggle_ir_light(self):
        """ПреONючва IR светлината ЧРЕЗ CGI КОМАНДИ"""
        # Проверка за cooldown (1 секунда)
        if "ir_light" in self.button_cooldowns:
            if time.time() - self.button_cooldowns["ir_light"] < 1.0:
                return

        try:
            cam = self.get_current_camera()
            if cam is None:
                return

            cam["ir_light_status"] = not cam.get("ir_light_status", False)
            # Използване на CGI команди вместо PTZ
            cmd = "iron" if cam["ir_light_status"] else "iroff"
            self.cgi_cmd(cmd)  # Използваме CGI вместо PTZ
            self.set_status(f"IR Light: {'ON' if cam['ir_light_status'] else 'OFF'}")
            # Задаване на cooldown (1 секунда)
            self.button_cooldowns["ir_light"] = time.time()
        except Exception as e:
            print(f"Грешка при преONючване на IR светлината: {e}")
            traceback.print_exc()

    def toggle_day_night(self):
        if "day_night" in self.button_cooldowns:
            if time.time() - self.button_cooldowns["day_night"] < 1.0:
                return

        try:
            cam = self.get_current_camera()
            if cam is None:
                return

            cam["day_night_status"] = not cam.get("day_night_status", True)
            cmd = "ircut?mode=day" if cam["day_night_status"] else "ircut?mode=night"
            self.cgi_cmd(cmd)
            self.set_status(f"MODE: {'Day' if cam['day_night_status'] else 'Night'}")
            self.button_cooldowns["day_night"] = time.time()
        except Exception as e:
            print(f"Грешка при преONючване на Day/Night MODE: {e}")
            traceback.print_exc()

    def update_ptz_position(self, cam_ip):
        try:
            cmd = (
                f"ssh root@{cam_ip} "
                '"ptz_test t >/dev/null; '
                "ptz_test p >/dev/null; "
                "dmesg 2>&1 "
                "| grep -E 'hmotor:|vmotor:' "
                "| tail -n2 "
                "| sed -n "
                "'s/.*hmotor:.*pos:\\([0-9]*\\).*/\\1/p; "
                "s/.*vmotor:.*pos:\\([0-9]*\\).*/\\1/p'; "
                'dmesg -c >/dev/null"'
            )

            result = subprocess.run(
                cmd,
                shell=True,
                capture_output=True,
                text=True,
                timeout=5,
            )

            if result.returncode == 0:
                lines = result.stdout.strip().splitlines()

                if len(lines) >= 2:
                    x = lines[0].strip()
                    y = lines[1].strip()

                    self.ptz_x = x
                    self.ptz_y = y

                    self.ptz_cache[cam_ip] = f"X={x} Y={y}"

                    print(f"PTZ: X={x} Y={y}")

                else:
                    print("PTZ parse failed:", repr(result.stdout))

            else:
                print("PTZ command failed:", result.stderr)

        except Exception as e:
            print("update_ptz_position:", e)

    def toggle_movement_blocking(self):
        self.movement_blocking_enabled = not self.movement_blocking_enabled
        self.set_status(
            f"Motion Tracking на движенията: {'ON' if self.movement_blocking_enabled else 'OFF'}"
        )
        self.save_config()
        self.button_cooldowns["movement_blocking"] = time.time()

    def validate_ipv4(self, ip):
        pattern = r"^(25[0-5]|2[0-4]\d|1?\d{1,2})(\.(25[0-5]|2[0-4]\d|1?\d{1,2})){3}$"
        return re.match(pattern, ip) is not None

    def main_loop(self):
        clock = pygame.time.Clock()

        # Стартираме всички Video Streamове за камерите
        for i in range(len(self.cameras)):
            # Стартираме мини видео потоци за всички камери
            self.start_mini_video_stream_async(i)
            time.sleep(0.5)  # Увеличено изчакване между стартиранията

        # ПреONючваме към първата камера
        if len(self.cameras) > 0:
            self.switch_camera(0)

        while self.running:
            try:
                # Handle white light timer
                if (
                    self.white_light_off_timer
                    and time.time() > self.white_light_off_timer
                ):
                    current_cam = self.get_current_camera()
                    if current_cam and current_cam.get("white_light_status", False):
                        self.toggle_white_light()
                    self.white_light_off_timer = None

                for event in pygame.event.get():
                    if event.type == pygame.QUIT:
                        self.cleanup_and_exit()
                        return

                    if event.type == pygame.VIDEORESIZE:
                        if not self.fullscreen_mode:
                            self.screen_width, self.screen_height = event.size
                            self.screen = pygame.display.set_mode(
                                (self.screen_width, self.screen_height),
                                pygame.RESIZABLE | pygame.DOUBLEBUF | pygame.HWSURFACE,
                            )

                    if event.type == pygame.MOUSEBUTTONDOWN:
                        if event.button == 1:
                            mouse_pos = pygame.mouse.get_pos()

                            # Обработка на кликване в Full Screen mode
                            if self.fullscreen_mode:
                                # Проверяваме дали е кликнато в контролите за Full Screen
                                controls = self.draw_fullscreen_controls(
                                    None
                                )  # Получаваме само правоъгълниците

                                if (
                                    controls
                                    and controls.get("exit")
                                    and controls["exit"].collidepoint(mouse_pos)
                                ):
                                    self.toggle_fullscreen()
                                elif (
                                    controls
                                    and controls.get("up")
                                    and controls["up"].collidepoint(mouse_pos)
                                ):
                                    self.send_ptz_command("3")
                                elif (
                                    controls
                                    and controls.get("down")
                                    and controls["down"].collidepoint(mouse_pos)
                                ):
                                    self.send_ptz_command("4")
                                elif (
                                    controls
                                    and controls.get("left")
                                    and controls["left"].collidepoint(mouse_pos)
                                ):
                                    self.send_ptz_command("1")
                                elif (
                                    controls
                                    and controls.get("right")
                                    and controls["right"].collidepoint(mouse_pos)
                                ):
                                    self.send_ptz_command("2")
                                elif (
                                    controls
                                    and controls.get("center")
                                    and controls["center"].collidepoint(mouse_pos)
                                ):
                                    self.send_ptz_command("0")
                                continue

                            panel_width = 250
                            right_start_y = 80
                            add_camera_y = right_start_y
                            ip_field_y = add_camera_y + 30
                            name_field_y = ip_field_y + 60

                            ip_field_rect = pygame.Rect(
                                self.screen_width - panel_width + 10,
                                ip_field_y,
                                panel_width - 30,
                                35,
                            )
                            name_field_rect = pygame.Rect(
                                self.screen_width - panel_width + 10,
                                name_field_y,
                                panel_width - 30,
                                35,
                            )

                            if ip_field_rect.collidepoint(mouse_pos):
                                self.input_active = "ip"
                            elif name_field_rect.collidepoint(mouse_pos):
                                self.input_active = "name"
                            else:
                                self.input_active = None

                                # Проверка за клик върху мини камера
                                for (
                                    camera_index,
                                    mini_rect,
                                ) in self.mini_camera_rects.items():
                                    if mini_rect.collidepoint(mouse_pos):
                                        camera = self.cameras[camera_index]

                                        # Switch to this camera
                                        self.switch_camera(camera_index)
                                        break

                        elif event.button == 4:
                            if "mouse_wheel_up" in self.button_cooldowns:
                                if (
                                    time.time()
                                    - self.button_cooldowns["mouse_wheel_up"]
                                    < 0.1
                                ):
                                    continue
                            self.zoom_in()
                            self.button_cooldowns["mouse_wheel_up"] = time.time()
                        elif event.button == 5:
                            if "mouse_wheel_down" in self.button_cooldowns:
                                if (
                                    time.time()
                                    - self.button_cooldowns["mouse_wheel_down"]
                                    < 0.1
                                ):
                                    continue
                            self.zoom_out()
                            self.button_cooldowns["mouse_wheel_down"] = time.time()

                    if event.type == pygame.TEXTINPUT:
                        if self.input_active == "ip":
                            self.ip_input += event.text
                        elif self.input_active == "name":
                            self.name_input += event.text

                    if event.type == pygame.KEYDOWN:
                        if event.key == pygame.K_ESCAPE:
                            if self.fullscreen_mode:
                                self.toggle_fullscreen()
                            else:
                                self.cleanup_and_exit()
                                return
                        elif event.key == pygame.K_f:
                            self.toggle_fullscreen()
                        elif event.key == pygame.K_i:
                            self.stop_intercom()
                        elif event.key in self.key_map:
                            cmd = self.key_map[event.key]
                            if cmd in self.button_cooldowns:
                                if time.time() - self.button_cooldowns[cmd] < 0.1:
                                    continue
                            self.pressed_buttons[cmd] = True
                            self.button_press_times[cmd] = time.time()
                            # Изпращаме командата веднага
                            if cmd in [
                                "0",
                                "1",
                                "2",
                                "3",
                                "4",
                                "5",
                                "6",
                                "7",
                                "8",
                                "9",
                                "a",
                            ]:
                                self.send_ptz_command(cmd)
                            self.start_button_thread(
                                cmd,
                                lambda c=cmd: None,  # Не изпълняваме нищо в нишката
                            )
                        elif event.key == pygame.K_x:
                            self.stop_all_movements()
                        if self.input_active:
                            if event.key == pygame.K_BACKSPACE:
                                if self.input_active == "ip":
                                    self.ip_input = self.ip_input[:-1]
                                elif self.input_active == "name":
                                    self.name_input = self.name_input[:-1]
                            elif event.key == pygame.K_RETURN:
                                self.add_new_camera_from_input()

                    elif event.type == pygame.KEYUP:
                        if event.key in self.key_map:
                            cmd = self.key_map[event.key]

                            self.release_button(cmd)

                            if cmd in ["0", "1", "2", "3", "4"]:
                                current_cam = self.get_current_camera()

                                if current_cam:
                                    cam_ip = current_cam["ip"]

                                    threading.Thread(
                                        target=self.update_ptz_position,
                                        args=(cam_ip,),
                                        daemon=True,
                                    ).start()

                        elif event.key == pygame.K_i:
                            self.stop_intercom()

                        elif event.key == pygame.K_x:
                            self.stop_all_movements()
                            self.stop_all_movements()
                        elif event.key == pygame.K_i:
                            self.stop_intercom()
                        elif event.key == pygame.K_x:
                            self.stop_all_movements()

                    if event.type == pygame.MOUSEBUTTONUP:
                        if event.button == 1:
                            self.release_all_buttons()

                            # Позволява алармата да бъде задействана отново
                            # при следващо натискане
                            self.alarm_triggered = False

                        if "slider_zoom" in self.button_cooldowns:
                            del self.button_cooldowns["slider_zoom"]

                    elif event.type == pygame.MOUSEWHEEL:
                        if event.y > 0:
                            self.zoom_in()
                        elif event.y < 0:
                            self.zoom_out()

                # Актуализираме всички мини Video Streamове
                for i, camera in enumerate(self.cameras):
                    # Проверяваме дали камерата е свързана
                    is_connected = (
                        camera.get("mini_cap") and camera["mini_cap"].isOpened()
                    ) or (camera.get("cap") and camera["cap"].isOpened())

                    if is_connected:
                        try:
                            # Използваме правилния каптур
                            cap = camera.get("mini_cap") or camera.get("cap")
                            if cap and cap.isOpened():
                                ret, frame = cap.read()
                                if ret and frame is not None:
                                    original_h, original_w = frame.shape[:2]

                                    # Малък размер за мини камери
                                    mini_w, mini_h = 180, 100

                                    # Поддържаме съотношението на страните
                                    aspect_ratio = original_w / original_h
                                    if mini_w / mini_h > aspect_ratio:
                                        new_h = mini_h
                                        new_w = int(mini_h * aspect_ratio)
                                    else:
                                        new_w = mini_w
                                        new_h = int(mini_w / aspect_ratio)

                                    frame_rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                                    temp_surf = pygame.image.frombuffer(
                                        frame_rgb.tobytes(),
                                        (original_w, original_h),
                                        "RGB",
                                    )
                                    scaled_surf = pygame.transform.scale(
                                        temp_surf, (new_w, new_h)
                                    )
                                    camera["mini_video_surface"] = scaled_surf
                                else:
                                    time.sleep(0.5)  # Увеличено изчакване при грешка
                        except Exception as e:
                            time.sleep(0.1)  # По-дълго изчакване при грешка

                # Актуализираме основния Video Stream
                cam = self.get_current_camera()
                if cam and (cam.get("cap") and cam["cap"].isOpened()):
                    try:
                        ret, frame = cam["cap"].read()
                        if ret and frame is not None:
                            # Запазваме последния кадър за използваване при визуализация
                            self.last_frame = frame.copy()
                            original_h, original_w = frame.shape[:2]

                            target_display_area_width = 0
                            target_display_area_height = 0
                            if self.fullscreen_mode:
                                info = pygame.display.Info()
                                (
                                    target_display_area_width,
                                    target_display_area_height,
                                ) = info.current_w, info.current_h
                            else:
                                panel_width = 250
                                target_display_area_width = (
                                    self.screen_width - 2 * panel_width - 40
                                )
                                target_display_area_height = self.screen_height - 120

                            target_display_area_width = max(
                                1, target_display_area_width
                            )
                            target_display_area_height = max(
                                1, target_display_area_height
                            )

                            frame_aspect_ratio = original_w / original_h
                            if (
                                target_display_area_width / target_display_area_height
                                > frame_aspect_ratio
                            ):
                                current_displayed_w = int(
                                    target_display_area_height * frame_aspect_ratio
                                )
                                current_displayed_h = target_display_area_height
                            else:
                                current_displayed_w = target_display_area_width
                                current_displayed_h = int(
                                    target_display_area_width / frame_aspect_ratio
                                )

                            current_displayed_w = max(1, current_displayed_w)
                            current_displayed_h = max(1, current_displayed_h)

                            if self.fullscreen_mode:
                                self.video_offset_x = (
                                    target_display_area_width - current_displayed_w
                                ) // 2
                                self.video_offset_y = (
                                    target_display_area_height - current_displayed_h
                                ) // 2
                            else:
                                panel_width = 250
                                self.video_offset_x = (
                                    panel_width
                                    + 20
                                    + (target_display_area_width - current_displayed_w)
                                    // 2
                                )
                                self.video_offset_y = (
                                    50
                                    + (target_display_area_height - current_displayed_h)
                                    // 2
                                )

                            self.video_surface_width = current_displayed_w
                            self.video_surface_height = current_displayed_h

                            current_zoom_factor = cam.get("current_zoom", 0.1)
                            if current_zoom_factor > 0.1:
                                processed_frame = self.apply_zoom(
                                    frame,
                                    current_zoom_factor,
                                )
                            else:
                                processed_frame = frame

                            frame_rgb = cv2.cvtColor(processed_frame, cv2.COLOR_BGR2RGB)

                            temp_surf = pygame.image.frombuffer(
                                frame_rgb.tobytes(),
                                (original_w, original_h),
                                "RGB",
                            )

                            scaled_surf = pygame.transform.scale(
                                temp_surf, (current_displayed_w, current_displayed_h)
                            )

                            cam["video_surface"] = scaled_surf
                            self.video_surface = scaled_surf

                        else:
                            time.sleep(0.5)  # Увеличено изчакване при грешка
                    except Exception as e:
                        print(f"Грешка при четене на кадър: {e}")
                        traceback.print_exc()
                        time.sleep(0.7)  # По-дълго изчакване при грешка
                else:
                    time.sleep(0.4)  # По-дълго изчакване когато няма връзка

                if self.fullscreen_mode:
                    self.render_fullscreen()
                else:
                    self.render_ui()

                if time.time() - self.status_timer > 5:
                    self.status_message = "Готов за работа"
                    self.status_timer = time.time()

                clock.tick(12)

            except Exception as e:
                traceback.print_exc()
                time.sleep(0.5)
                self.cleanup_and_exit()


if __name__ == "__main__":
    try:
        controller = CameraController()
    except KeyboardInterrupt:
        print("Приложението е спряно от потребителя")
    except Exception as e:
        print(f"Фатална грешка: {e}")
        traceback.print_exc()

