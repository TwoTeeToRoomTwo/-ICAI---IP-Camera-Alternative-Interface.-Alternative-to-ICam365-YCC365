import os
import re
import subprocess
import threading
import tkinter as tk

from ftplib import FTP
from pathlib import PurePosixPath
from tkinter import ttk, filedialog, messagebox


class RecordingsBrowser(tk.Toplevel):
    # ROOT_PATH = "/tmp/mnt"
    FTP_USER = "root"
    FTP_PASSWORD = "cxlinux"

    def __init__(self, parent, camera):
        super().__init__(parent)

        self.parent = parent
        self.camera = camera
        self.ftp = None

        self.title("Преглед на записи")
        self.geometry("950x600")
        self.minsize(700, 450)

        self.create_widgets()

        # Зареждане на записите в отделен thread,
        # за да не блокира главният прозорец.
        self.load_recordings()

    def create_widgets(self):
        """Създава интерфейса на файловия мениджър."""

        main_frame = ttk.Frame(self, padding=10)
        main_frame.pack(fill="both", expand=True)

        toolbar = ttk.Frame(main_frame)
        toolbar.pack(fill="x", pady=(0, 8))

        self.refresh_button = ttk.Button(
            toolbar, text="Обнови", command=self.load_recordings
        )
        self.refresh_button.pack(side="left", padx=(0, 5))

        self.open_button = ttk.Button(
            toolbar, text="Отвори", command=self.open_selected
        )
        self.open_button.pack(side="left", padx=5)

        self.play_button = ttk.Button(
            toolbar, text="Стартирай видео", command=self.play_selected
        )
        self.play_button.pack(side="left", padx=5)

        self.copy_button = ttk.Button(
            toolbar, text="Копирай локално", command=self.copy_selected
        )
        self.copy_button.pack(side="left", padx=5)

        self.delete_button = ttk.Button(
            toolbar, text="Изтрий", command=self.delete_selected
        )
        self.delete_button.pack(side="left", padx=5)

        ttk.Button(toolbar, text="Затвори", command=self.destroy).pack(side="right")

        tree_frame = ttk.Frame(main_frame)
        tree_frame.pack(fill="both", expand=True)

        self.tree = ttk.Treeview(
            tree_frame,
            columns=("type", "path"),
            show="tree headings",
            selectmode="browse",
        )

        self.tree.heading("#0", text="Име")
        self.tree.heading("type", text="Тип")
        self.tree.heading("path", text="FTP път")

        self.tree.column("#0", width=280, anchor="w")
        self.tree.column("type", width=100, anchor="w")
        self.tree.column("path", width=500, anchor="w")

        vertical_scrollbar = ttk.Scrollbar(
            tree_frame, orient="vertical", command=self.tree.yview
        )

        horizontal_scrollbar = ttk.Scrollbar(
            tree_frame, orient="horizontal", command=self.tree.xview
        )

        self.tree.configure(
            yscrollcommand=vertical_scrollbar.set,
            xscrollcommand=horizontal_scrollbar.set,
        )

        self.tree.grid(row=0, column=0, sticky="nsew")
        vertical_scrollbar.grid(row=0, column=1, sticky="ns")
        horizontal_scrollbar.grid(row=1, column=0, sticky="ew")

        tree_frame.rowconfigure(0, weight=1)
        tree_frame.columnconfigure(0, weight=1)

        self.status_label = ttk.Label(main_frame, text="Зареждане...")
        self.status_label.pack(fill="x", pady=(8, 0))

        self.tree.bind("<Double-1>", self.on_double_click)

        # Контекстно меню с десен бутон.
        self.context_menu = tk.Menu(self, tearoff=False)

        self.context_menu.add_command(label="Отвори", command=self.open_selected)

        self.context_menu.add_command(
            label="Стартирай видео", command=self.play_selected
        )

        self.context_menu.add_command(
            label="Копирай локално", command=self.copy_selected
        )

        self.context_menu.add_separator()

        self.context_menu.add_command(label="Изтрий", command=self.delete_selected)

        self.tree.bind("<Button-3>", self.show_context_menu)

    # ------------------------------------------------------------------
    # FTP помощни методи
    # ------------------------------------------------------------------

    def connect_ftp(self):
        """Свързва се към FTP на текущата камера."""

        camera_ip = self.camera.get("ip")

        if not camera_ip:
            raise ValueError("Липсва IP адрес на текущата камера.")

        ftp = FTP()

        # По желание за диагностика:
        ftp.set_debuglevel(1)

        print(f"Свързване към FTP: {camera_ip}:21")

        ftp.connect(
            host=camera_ip,
            port=21,
            timeout=40,
        )

        ftp.login(
            user=self.FTP_USER,
            passwd=self.FTP_PASSWORD,
        )

        # Използва passive FTP режим
        ftp.set_pasv(True)

        print("FTP входът е успешен.")

        return ftp

    def ftp_dir_entries(self, ftp):
        """Връща съдържанието на текущата FTP директория."""

        entries = []

        def parse_line(line):
            print("FTP:", line)

            parts = line.split()

            if not parts:
                return

            name = parts[-1]

            if name in (".", ".."):
                return

            is_directory = line.startswith("d")

            entries.append((name, is_directory))

        ftp.dir(parse_line)

        return entries

    def ftp_list_entries(self, ftp, path):
        """
        Извлича FTP съдържанието на path.

        Връща:
            [
                ("име", True),   # директория
                ("име.mp4", False)  # файл
            ]
        """

        entries = []

        def parse_line(line):
            parts = line.split()

            if not parts:
                return

            name = parts[-1]

            if name in (".", ".."):
                return

            # Unix FTP LIST формат:
            # директорията започва с d
            is_directory = line.startswith("d")

            entries.append((name, is_directory))

        ftp.dir(path, parse_line)

        return entries

        def parse_line(line):
            parts = line.split()

            if not parts:
                return

            name = parts[-1]

            if name in (".", ".."):
                return

            # Unix FTP LIST ред за директория започва с d:
            # drwxr-xr-x ...
            is_directory = line.startswith("d")

            entries.append((name, is_directory))

        ftp.dir(parse_line)

        return entries

    # ------------------------------------------------------------------
    # Зареждане на папките и файловете
    # ------------------------------------------------------------------

    def load_recordings(self):
        """Зарежда записите от камерата."""

        self.set_buttons_state("disabled")
        self.status_label.configure(text="Свързване с камерата...")

        for item in self.tree.get_children():
            self.tree.delete(item)

        thread = threading.Thread(target=self.load_recordings_thread, daemon=True)
        thread.start()

    def load_recordings_thread(self):
        """Зарежда записите от FTP камерата."""

        ftp = None
        result = []

        try:
            ftp = self.connect_ftp()

            root_path = "/tmp/mnt"

            # Еквивалент на:
            # cd /tmp/mnt/
            ftp.cwd(root_path)

            print(f"FTP текуща директория: {ftp.pwd()}")

            # Еквивалент на: dir
            root_entries = self.ftp_dir_entries(ftp)

            date_directories = [
                name
                for name, is_directory in root_entries
                if (
                    is_directory
                    and re.fullmatch(
                        r"20\d{2}-\d{2}-\d{2}",
                        name,
                    )
                )
            ]

            print(f"Намерени папки с дати: {date_directories}")

            date_directories.sort(reverse=True)

            for date_directory in date_directories:
                try:
                    # Еквивалент на:
                    # cd /tmp/mnt/$d
                    ftp.cwd(root_path)
                    ftp.cwd(date_directory)

                    date_path = f"{root_path}/{date_directory}"

                    subdirectories = [
                        name
                        for name, is_directory in self.ftp_dir_entries(ftp)
                        if is_directory
                    ]

                    print(f"Подпапки в {date_path}: {subdirectories}")

                    folder_data = {
                        "name": date_directory,
                        "type": "Папка",
                        "path": date_path,
                        "children": [],
                    }

                    for subdirectory in subdirectories:
                        try:
                            # Връщаме се към конкретната дата
                            ftp.cwd(root_path)
                            ftp.cwd(date_directory)
                            ftp.cwd(subdirectory)

                            subdirectory_path = f"{date_path}/{subdirectory}"

                            file_entries = self.ftp_dir_entries(ftp)

                            for filename, is_directory in file_entries:
                                if not is_directory and filename.lower().endswith(
                                    ".mp4"
                                ):
                                    folder_data["children"].append(
                                        {
                                            "name": filename,
                                            "type": "Видео",
                                            "path": (f"{subdirectory_path}/{filename}"),
                                        }
                                    )

                        except Exception as e:
                            print(f"Грешка при четене на {subdirectory}: {e}")

                    if folder_data["children"]:
                        result.append(folder_data)

                except Exception as e:
                    print(f"Грешка при четене на {date_directory}: {e}")

            self.after(0, lambda: self.fill_tree(result))

        except Exception as e:
            error_text = f"FTP грешка: {type(e).__name__}: {e}"

            print(error_text)

            self.after(0, lambda error=error_text: self.show_status(error))

        finally:
            if ftp is not None:
                try:
                    ftp.quit()
                except Exception:
                    try:
                        ftp.close()
                    except Exception:
                        pass

            self.after(0, lambda: self.set_buttons_state("normal"))

    def fill_tree(self, folders):
        """Показва заредените папки и файлове в Treeview."""

        video_count = 0

        for folder in folders:
            folder_id = self.tree.insert(
                "",
                "end",
                text=folder["name"],
                values=(folder["type"], folder["path"]),
                open=False,
            )

            for video in folder["children"]:
                self.tree.insert(
                    folder_id,
                    "end",
                    text=video["name"],
                    values=(video["type"], video["path"]),
                )

                video_count += 1

        self.status_label.configure(
            text=(f"Намерени папки: {len(folders)} | Видео файлове: {video_count}")
        )

    # ------------------------------------------------------------------
    # Избор и отваряне
    # ------------------------------------------------------------------

    def get_selected_item(self):
        """Връща избрания елемент от дървото."""

        selection = self.tree.selection()

        if not selection:
            messagebox.showinfo("Избор", "Изберете папка или видео файл.", parent=self)
            return None

        item_id = selection[0]
        item_values = self.tree.item(item_id, "values")

        return {
            "id": item_id,
            "name": self.tree.item(item_id, "text"),
            "type": item_values[0],
            "path": item_values[1],
        }

    def open_selected(self):
        """Отваря избраната папка или стартира избраното видео."""

        item = self.get_selected_item()

        if not item:
            return

        if item["type"] == "Папка":
            is_open = self.tree.item(item["id"], "open")

            self.tree.item(item["id"], open=not is_open)
        else:
            self.play_selected()

    def on_double_click(self, event):
        self.open_selected()

    def show_context_menu(self, event):
        item_id = self.tree.identify_row(event.y)

        if item_id:
            self.tree.selection_set(item_id)
            self.context_menu.tk_popup(event.x_root, event.y_root)

    # ------------------------------------------------------------------
    # Изтегляне и стартиране на видео
    # ------------------------------------------------------------------

    def copy_selected(self):
        """Изтегля избрания MP4 файл локално."""

        item = self.get_selected_item()

        if not item:
            return

        if item["type"] != "Видео":
            messagebox.showinfo("Копиране", "Изберете видео файл.", parent=self)
            return

        destination_folder = filedialog.askdirectory(
            title="Изберете папка за копиране", parent=self
        )

        if not destination_folder:
            return

        destination = os.path.join(destination_folder, item["name"])

        self.set_buttons_state("disabled")
        self.show_status("Копиране на файла...")

        thread = threading.Thread(
            target=self.download_file_thread,
            args=(item["path"], destination, False),
            daemon=True,
        )
        thread.start()

    def play_selected(self):
        """Изтегля и стартира избраното видео."""

        item = self.get_selected_item()

        if not item:
            return

        if item["type"] != "Видео":
            messagebox.showinfo("Видео", "Изберете MP4 файл.", parent=self)
            return

        local_folder = os.path.join(os.path.expanduser("~"), "camera_recordings")

        os.makedirs(local_folder, exist_ok=True)

        destination = os.path.join(local_folder, item["name"])

        self.set_buttons_state("disabled")
        self.show_status("Изтегляне на видеото...")

        thread = threading.Thread(
            target=self.download_file_thread,
            args=(item["path"], destination, True),
            daemon=True,
        )
        thread.start()

    def download_file_thread(self, remote_path, destination, play_after_download):
        """Изтегля файл от камерата чрез FTP."""

        ftp = None

        try:
            ftp = self.connect_ftp()

            remote_directory = str(PurePosixPath(remote_path).parent)
            remote_filename = PurePosixPath(remote_path).name

            ftp.cwd(remote_directory)

            with open(destination, "wb") as output_file:
                ftp.retrbinary(f"RETR {remote_filename}", output_file.write)

            self.after(
                0,
                lambda path=destination: self.download_finished(
                    path, play_after_download
                ),
            )

        except Exception as e:
            self.after(
                0,
                lambda error=str(e): self.show_status(f"Грешка при изтегляне: {error}"),
            )

        finally:
            if ftp is not None:
                try:
                    ftp.quit()
                except Exception:
                    try:
                        ftp.close()
                    except Exception:
                        pass

            self.after(0, lambda: self.set_buttons_state("normal"))

    def download_finished(self, filename, play_after_download):
        self.show_status(f"Файлът е записан в:\n{filename}")

        if play_after_download:
            self.play_video(filename)

    def play_video(self, filename):
        """Стартира видеото с плеъра по подразбиране."""

        try:
            if os.name == "nt":
                os.startfile(filename)

            elif os.name == "posix":
                subprocess.Popen(
                    ["xdg-open", filename],
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                )

            else:
                messagebox.showinfo(
                    "Видео", f"Файлът е записан в:\n{filename}", parent=self
                )

        except Exception as e:
            messagebox.showerror(
                "Грешка", f"Не може да бъде стартирано видеото:\n{e}", parent=self
            )

    # ------------------------------------------------------------------
    # Изтриване
    # ------------------------------------------------------------------

    def delete_selected(self):
        """Изтрива избран файл или цяла папка."""

        item = self.get_selected_item()

        if not item:
            return

        answer = messagebox.askyesno(
            "Потвърждение",
            (f"Това действие е необратимо.\n\nДа бъде ли изтрито:\n{item['name']}?"),
            parent=self,
        )

        if not answer:
            return

        self.set_buttons_state("disabled")
        self.show_status("Изтриване...")

        thread = threading.Thread(
            target=self.delete_selected_thread, args=(item,), daemon=True
        )
        thread.start()

    def delete_selected_thread(self, item):
        """FTP изтриване в отделен thread."""

        ftp = None

        try:
            ftp = self.connect_ftp()

            remote_path = item["path"]
            parent_path = str(PurePosixPath(remote_path).parent)
            name = PurePosixPath(remote_path).name

            ftp.cwd(parent_path)

            if item["type"] == "Видео":
                ftp.delete(name)

            elif item["type"] == "Папка":
                self.delete_ftp_directory(ftp, name)

            self.after(0, lambda item_id=item["id"]: self.remove_tree_item(item_id))

        except Exception as e:
            self.after(
                0,
                lambda error=str(e): self.show_status(f"Грешка при изтриване: {error}"),
            )

        finally:
            if ftp is not None:
                try:
                    ftp.quit()
                except Exception:
                    try:
                        ftp.close()
                    except Exception:
                        pass

            self.after(0, lambda: self.set_buttons_state("normal"))

    def delete_ftp_directory(self, ftp, dirname):
        """
        Рекурсивно изтрива FTP директорията dirname.

        При извикване текущата директория трябва да бъде
        родителската директория на dirname.
        """

        parent_path = ftp.pwd()

        ftp.cwd(dirname)

        entries = self.ftp_list_entries(ftp)

        for name, is_directory in entries:
            if is_directory:
                self.delete_ftp_directory(ftp, name)
            else:
                ftp.delete(name)

        ftp.cwd(parent_path)
        ftp.rmd(dirname)

    def remove_tree_item(self, item_id):
        self.tree.delete(item_id)
        self.show_status("Изтриването приключи успешно.")

    # ------------------------------------------------------------------
    # Интерфейс
    # ------------------------------------------------------------------

    def set_buttons_state(self, state):
        for button in (
            self.refresh_button,
            self.open_button,
            self.play_button,
            self.copy_button,
            self.delete_button,
        ):
            button.configure(state=state)

    def show_status(self, text):
        self.status_label.configure(text=text)


if __name__ == "__main__":
    import sys
    import tkinter as tk
    from tkinter import messagebox

    if len(sys.argv) < 2:
        root = tk.Tk()
        root.withdraw()

        messagebox.showerror("Грешка", "Не е подаден IP адрес на камерата.")

        root.destroy()
        sys.exit(1)

    camera_ip = sys.argv[1]

    root = tk.Tk()
    root.withdraw()

    camera = {"ip": camera_ip}

    browser = RecordingsBrowser(parent=root, camera=camera)

    def close_application():
        try:
            browser.destroy()
        except Exception:
            pass

        root.destroy()

    browser.protocol("WM_DELETE_WINDOW", close_application)

    root.mainloop()
