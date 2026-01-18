import os
import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext

# Try to import clipboard support
try:
    import pyperclip
    HAS_CLIPBOARD = True
except ImportError:
    HAS_CLIPBOARD = False

# ================= CONFIGURATION =================
EXTENSIONS = {".lean"}
IGNORE_DIRS = {".git", "build", "lake-packages", ".lake", "__pycache__", ".DS_Store"}
# =================================================

class LeanContextApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Lean 4 Context Gatherer")
        self.root.geometry("1100x700")

        self.root_dir = os.getcwd()

        # ================= LAYOUT =================
        self.paned_window = ttk.PanedWindow(root, orient=tk.HORIZONTAL)
        self.paned_window.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        # --- LEFT FRAME ---
        self.left_frame = ttk.Frame(self.paned_window, width=400)
        self.paned_window.add(self.left_frame, weight=1)

        # Inputs
        input_group = ttk.LabelFrame(self.left_frame, text="Search Criteria", padding=10)
        input_group.pack(fill=tk.X, pady=5)

        ttk.Label(input_group, text="Content Keywords (comma separated):").pack(anchor="w")
        self.entry_keywords = ttk.Entry(input_group)
        self.entry_keywords.pack(fill=tk.X, pady=(0, 10))

        ttk.Label(input_group, text="Filename Filter (partial match):").pack(anchor="w")
        self.entry_filename = ttk.Entry(input_group)
        self.entry_filename.pack(fill=tk.X, pady=(0, 10))

        self.btn_scan = ttk.Button(input_group, text="🔍 Scan Directory", command=self.scan_files)
        self.btn_scan.pack(fill=tk.X)

        # Results List (Treeview for Mac support)
        list_group = ttk.LabelFrame(self.left_frame, text="Found Files (Cmd+Click to Multi-Select)", padding=10)
        list_group.pack(fill=tk.BOTH, expand=True, pady=5)

        self.listbox_frame = ttk.Frame(list_group)
        self.listbox_frame.pack(fill=tk.BOTH, expand=True)
        
        self.scrollbar = ttk.Scrollbar(self.listbox_frame)
        self.scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.tree = ttk.Treeview(
            self.listbox_frame, 
            selectmode="extended", 
            show="tree",
            yscrollcommand=self.scrollbar.set
        )
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.scrollbar.config(command=self.tree.yview)

        # Helper buttons
        btn_frame = ttk.Frame(list_group)
        btn_frame.pack(fill=tk.X, pady=5)
        ttk.Button(btn_frame, text="Select All", command=self.select_all).pack(side=tk.LEFT, expand=True)
        ttk.Button(btn_frame, text="Clear Selection", command=self.clear_selection).pack(side=tk.LEFT, expand=True)

        self.btn_generate = ttk.Button(self.left_frame, text="➡️ Generate Prompt from Selection", command=self.generate_prompt)
        self.btn_generate.pack(fill=tk.X, pady=10)

        # --- RIGHT FRAME ---
        self.right_frame = ttk.Frame(self.paned_window, width=600)
        self.paned_window.add(self.right_frame, weight=2)

        output_group = ttk.LabelFrame(self.right_frame, text="Generated Prompt", padding=10)
        output_group.pack(fill=tk.BOTH, expand=True)

        self.text_output = scrolledtext.ScrolledText(output_group, wrap=tk.WORD, font=("Menlo", 12))
        self.text_output.pack(fill=tk.BOTH, expand=True, pady=(0, 10))

        bottom_bar = ttk.Frame(output_group)
        bottom_bar.pack(fill=tk.X)

        self.lbl_stats = ttk.Label(bottom_bar, text="Tokens: 0 | Chars: 0")
        self.lbl_stats.pack(side=tk.LEFT)

        self.btn_copy = ttk.Button(bottom_bar, text="📋 Copy to Clipboard", command=self.copy_to_clipboard)
        self.btn_copy.pack(side=tk.RIGHT)

        self.item_map = {} 

    # ================= LOGIC =================

    def read_file_safely(self, filepath):
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                return f.read()
        except Exception:
            return None

    def scan_files(self):
        raw_keywords = self.entry_keywords.get()
        keywords = [k.strip() for k in raw_keywords.split(",") if k.strip()]
        filename_filter = self.entry_filename.get().strip()

        # Clear Treeview
        for item in self.tree.get_children():
            self.tree.delete(item)
        self.item_map = {}

        matched_files = []
        
        self.root.config(cursor="watch")
        self.root.update()

        for root, dirs, files in os.walk(self.root_dir):
            dirs[:] = [d for d in dirs if d not in IGNORE_DIRS]
            
            for file in files:
                if os.path.splitext(file)[1] in EXTENSIONS:
                    full_path = os.path.join(root, file)
                    rel_path = os.path.relpath(full_path, self.root_dir)

                    if filename_filter and filename_filter.lower() not in rel_path.lower():
                        continue

                    if keywords:
                        content = self.read_file_safely(full_path)
                        if not content: continue
                        if not any(k in content for k in keywords):
                            continue
                    
                    matched_files.append((rel_path, full_path))

        matched_files.sort()
        for rel_path, full_path in matched_files:
            item_id = self.tree.insert("", tk.END, text=rel_path)
            self.item_map[item_id] = (rel_path, full_path)
        
        self.select_all()

        self.root.config(cursor="")
        self.root.title(f"Lean 4 Context Gatherer - Found {len(matched_files)} files")

    def select_all(self):
        children = self.tree.get_children()
        if children:
            self.tree.selection_set(children)

    def clear_selection(self):
        self.tree.selection_set()

    def generate_prompt(self):
        selected_items = self.tree.selection()
        
        if not selected_items:
            messagebox.showwarning("No Selection", "Please select at least one file from the list.")
            return

        output_parts = []
        output_parts.append("I am providing a subset of my Lean 4 codebase. Please use these files as context.\n")
        
        for item_id in selected_items:
            rel_path, full_path = self.item_map[item_id]
            content = self.read_file_safely(full_path)
            
            if content:
                block = f"<file path=\"{rel_path}\">\n{content}\n</file>\n\n"
                output_parts.append(block)

        final_prompt = "".join(output_parts)
        
        self.text_output.delete("1.0", tk.END)
        self.text_output.insert("1.0", final_prompt)
        
        total_chars = len(final_prompt)
        est_tokens = total_chars // 4
        self.lbl_stats.config(text=f"Tokens: ~{est_tokens} | Chars: {total_chars}")

    def copy_to_clipboard(self):
        """Copies text and gives visual feedback on the button instead of a popup."""
        text = self.text_output.get("1.0", tk.END)
        
        if HAS_CLIPBOARD:
            pyperclip.copy(text)
            
            # Save original text
            original_text = "📋 Copy to Clipboard"
            
            # Change button text to indicate success
            self.btn_copy.config(text="✅ Copied!")
            
            # Change it back after 1.5 seconds (1500 milliseconds)
            self.root.after(1500, lambda: self.btn_copy.config(text=original_text))
        else:
            messagebox.showerror("Error", "pyperclip module not found. \nPlease run 'pip install pyperclip'")

if __name__ == "__main__":
    root = tk.Tk()
    app = LeanContextApp(root)
    root.mainloop()