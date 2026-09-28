#![windows_subsystem = "windows"]

use std::collections::HashMap;
use std::fs::{self, File};
use std::io::{self, IsTerminal, Read, Seek, SeekFrom, Write};
use std::panic;
use std::path::Path;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread::{self, sleep};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use discord_rich_presence::activity::{Activity, Assets, Timestamps};
use discord_rich_presence::{DiscordIpc, DiscordIpcClient};
use sysinfo::System;

const DISCORD_APP_ID: &str = "1553962630828531742";
const POLL_INTERVAL: Duration = Duration::from_millis(1000);

#[allow(non_upper_case_globals)]
pub const CrashOnCtrlDel: bool = true;

#[derive(Debug, Clone, Default)]
pub struct LiveGameState {
    pub chapter: u32,
    pub room_id: Option<i32>,
    pub room_name: Option<String>,
    pub in_battle: bool,
}

// Convert GameMaker room names and battle state to string
fn get_state(raw_room: Option<&str>, in_battle: bool, chapter: u32) -> String {
    if in_battle {
        return "In Battle".to_string();
    }

    let raw = match raw_room {
        Some(r) => r,
        None => {
            return if chapter == 0 {
                "In Chapter Select".to_string()
            } else {
                "In Adventure".to_string()
            };
        }
    };

    let lower = raw.to_lowercase();
    if lower.contains("battle") {
        return "In Battle".to_string();
    }
    if lower.contains("chapter_select") || lower.contains("place_chapter") {
        return "In Chapter Select".to_string();
    }
    if lower.contains("place_menu") || lower.contains("menu") || lower.contains("title") {
        return "In Title Screen".to_string();
    }

    let mut clean = raw.trim();
    if let Some(rest) = clean.strip_prefix("room_") {
        clean = rest;
    }
    if let Some(rest) = clean.strip_prefix("dw_") {
        clean = rest;
    } else if let Some(rest) = clean.strip_prefix("lw_") {
        clean = rest;
    }

    let words: Vec<String> = clean
        .split('_')
        .map(|w| {
            let mut c = w.chars();
            match c.next() {
                None => String::new(),
                Some(f) => f.to_uppercase().collect::<String>() + c.as_str(),
            }
        })
        .collect();

    format!("In {}", words.join(" "))
}

// Parse room name map from data.win file
fn parse_rooms(data_win_path: &Path) -> HashMap<i32, String> {
    let mut rooms = HashMap::new();
    let data = match fs::read(data_win_path) {
        Ok(d) => d,
        Err(_) => return rooms,
    };

    let room_idx = match data.windows(4).position(|w| w == b"ROOM") {
        Some(idx) => idx,
        None => return rooms,
    };

    if room_idx + 12 > data.len() {
        return rooms;
    }

    let count = u32::from_le_bytes(data[room_idx + 8..room_idx + 12].try_into().unwrap()) as usize;
    let offsets_start = room_idx + 12;

    for i in 0..count {
        let entry_pos = offsets_start + i * 4;
        if entry_pos + 4 > data.len() {
            break;
        }

        let roff = u32::from_le_bytes(data[entry_pos..entry_pos + 4].try_into().unwrap()) as usize;
        if roff + 4 > data.len() {
            continue;
        }

        let name_ptr = u32::from_le_bytes(data[roff..roff + 4].try_into().unwrap()) as usize;
        if name_ptr < data.len() {
            let end = data[name_ptr..]
                .iter()
                .position(|&b| b == 0)
                .map(|p| name_ptr + p)
                .unwrap_or(data.len().min(name_ptr + 64));

            if let Ok(name) = std::str::from_utf8(&data[name_ptr..end]) {
                rooms.insert(i as i32, name.to_string());
            }
        }
    }

    rooms
}

// Parse battle controller object IDs from data.win OBJT chunk
fn parse_battle_obj(data_win_path: &Path) -> Vec<i32> {
    let mut ids = Vec::new();
    let data = match fs::read(data_win_path) {
        Ok(d) => d,
        Err(_) => return ids,
    };

    let obj_idx = match data.windows(4).position(|w| w == b"OBJT") {
        Some(idx) => idx,
        None => return ids,
    };

    if obj_idx + 12 > data.len() {
        return ids;
    }

    let count = u32::from_le_bytes(data[obj_idx + 8..obj_idx + 12].try_into().unwrap()) as usize;
    let offsets_start = obj_idx + 12;

    for i in 0..count {
        let entry_pos = offsets_start + i * 4;
        if entry_pos + 4 > data.len() {
            break;
        }

        let roff = u32::from_le_bytes(data[entry_pos..entry_pos + 4].try_into().unwrap()) as usize;
        if roff + 4 > data.len() {
            continue;
        }

        let name_ptr = u32::from_le_bytes(data[roff..roff + 4].try_into().unwrap()) as usize;
        if name_ptr < data.len() {
            let end = data[name_ptr..]
                .iter()
                .position(|&b| b == 0)
                .map(|p| name_ptr + p)
                .unwrap_or(data.len().min(name_ptr + 64));

            if let Ok(name) = std::str::from_utf8(&data[name_ptr..end]) {
                if name == "obj_battlecontroller"
                    || name == "obj_tensionbar"
                    || name == "obj_monsterparent"
                {
                    ids.push(i as i32);
                }
            }
        }
    }

    ids
}

// Memory reader for DELTARUNE process
struct MemoryInspector {
    pid: u32,
    mem_file: Option<File>,
    room_var_addr: Option<u64>,
    last_battle_check: Instant,
    cached_battle_state: bool,
}

impl MemoryInspector {
    fn new(pid: u32) -> Self {
        let mem_path = format!("/proc/{pid}/mem");
        let mem_file = File::open(mem_path).ok();
        Self {
            pid,
            mem_file,
            room_var_addr: None,
            last_battle_check: Instant::now() - Duration::from_secs(10),
            cached_battle_state: false,
        }
    }

    fn ensure_file(&mut self) -> Option<&mut File> {
        if self.mem_file.is_none() {
            let mem_path = format!("/proc/{}/mem", self.pid);
            self.mem_file = File::open(mem_path).ok();
        }
        self.mem_file.as_mut()
    }

    // Dynamically resolve GameMaker's global "room" integer address via the engine's built-in table
    fn resolve_room_address(&mut self) -> Option<u64> {
        if let Some(addr) = self.room_var_addr {
            return Some(addr);
        }

        let maps_path = format!("/proc/{}/maps", self.pid);
        let maps_content = fs::read_to_string(maps_path).ok()?;
        let mem_file = self.ensure_file()?;

        let mut str_candidates: Vec<u64> = Vec::new();

        /////////////////////////////////

        for line in maps_content.lines() {
            if !line.contains("rw-p") && !line.contains("r--p") {
                continue;
            }

            let mut parts = line.split_whitespace();
            let range = match parts.next() {
                Some(r) => r,
                None => continue,
            };
            let mut range_parts = range.split('-');
            let start = match range_parts.next().and_then(|s| u64::from_str_radix(s, 16).ok()) {
                Some(v) => v,
                None => continue,
            };
            let end = match range_parts.next().and_then(|s| u64::from_str_radix(s, 16).ok()) {
                Some(v) => v,
                None => continue,
            };

            let size = end.saturating_sub(start);
            if size == 0 || size > 16 * 1024 * 1024 {
                continue;
            }

            let mut buf = vec![0u8; size as usize];
            if mem_file.seek(SeekFrom::Start(start)).is_err() || mem_file.read_exact(&mut buf).is_err() {
                continue;
            }

            let mut p = 0;
            while let Some(idx) = buf[p..].windows(8).position(|w| w == b"\x00room\x00\x00\x00") {
                str_candidates.push(start + (p + idx + 1) as u64);
                p += idx + 8;
            }
        }

        /////////////////////////////////

        for s_addr in str_candidates {
            let s_bytes = s_addr.to_le_bytes();

            for line in maps_content.lines() {
                if !line.contains("rw-p") && !line.contains("r--p") {
                    continue;
                }

                let mut parts = line.split_whitespace();
                let range = match parts.next() {
                    Some(r) => r,
                    None => continue,
                };
                let mut range_parts = range.split('-');
                let start = match range_parts.next().and_then(|s| u64::from_str_radix(s, 16).ok()) {
                    Some(v) => v,
                    None => continue,
                };
                let end = match range_parts.next().and_then(|s| u64::from_str_radix(s, 16).ok()) {
                    Some(v) => v,
                    None => continue,
                };

                let size = end.saturating_sub(start);
                if size == 0 || size > 32 * 1024 * 1024 {
                    continue;
                }

                let mut buf = vec![0u8; size as usize];
                if mem_file.seek(SeekFrom::Start(start)).is_err() || mem_file.read_exact(&mut buf).is_err() {
                    continue;
                }

                let mut idx = 0;
                while let Some(p) = buf[idx..].windows(8).position(|w| w == s_bytes) {
                    let entry_offset = idx + p;
                    if entry_offset + 16 <= buf.len() {
                        let fn_ptr = u64::from_le_bytes(buf[entry_offset + 8..entry_offset + 16].try_into().unwrap());
                        if fn_ptr >= 0x140000000 && fn_ptr <= 0x140200000 {
                            let mut fn_bytes = [0u8; 24];
                            if mem_file.seek(SeekFrom::Start(fn_ptr)).is_ok()
                                && mem_file.read_exact(&mut fn_bytes).is_ok()
                            {
                                if let Some(op_pos) = fn_bytes.windows(4).position(|w| w == [0x66, 0x0f, 0x6e, 0x05]) {
                                    let rel = i32::from_le_bytes(fn_bytes[op_pos + 4..op_pos + 8].try_into().unwrap());
                                    let target_addr = (fn_ptr as i64 + op_pos as i64 + 8 + rel as i64) as u64;
                                    self.room_var_addr = Some(target_addr);
                                    return Some(target_addr);
                                }
                            }
                        }
                    }
                    idx += p + 8;
                }
            }
        }

        None
    }

    fn read_room_id(&mut self) -> Option<i32> {
        let addr = self.resolve_room_address()?;
        let file = self.ensure_file()?;
        file.seek(SeekFrom::Start(addr)).ok()?;
        let mut buf = [0u8; 4];
        file.read_exact(&mut buf).ok()?;
        Some(i32::from_le_bytes(buf))
    }

    // Detect if DELTARUNE is currently in battle by scanning CInstance memory for battle controller instances
    fn check_in_battle(&mut self, battle_obj_ids: &[i32]) -> bool {
        if battle_obj_ids.is_empty() {
            return false;
        }

        if self.last_battle_check.elapsed() < Duration::from_millis(800) {
            return self.cached_battle_state;
        }
        self.last_battle_check = Instant::now();

        let maps_path = format!("/proc/{}/maps", self.pid);
        let maps_content = match fs::read_to_string(maps_path) {
            Ok(c) => c,
            Err(_) => return false,
        };
        let file = match self.ensure_file() {
            Some(f) => f,
            None => return false,
        };

        for line in maps_content.lines() {
            if !line.contains("rw-p")
                || line.contains("[heap]")
                || line.contains("[stack]")
                || line.contains("/usr/")
                || line.contains("/lib")
                || line.contains(".so")
                || line.contains(".dll")
                || line.contains("Proton")
                || line.contains("DELTARUNE")
                || line.contains("steam")
            {
                continue;
            }

            let mut parts = line.split_whitespace();
            let range = match parts.next() {
                Some(r) => r,
                None => continue,
            };
            let mut range_parts = range.split('-');
            let start = match range_parts.next().and_then(|s| u64::from_str_radix(s, 16).ok()) {
                Some(v) => v,
                None => continue,
            };
            let end = match range_parts.next().and_then(|s| u64::from_str_radix(s, 16).ok()) {
                Some(v) => v,
                None => continue,
            };

            let size = end.saturating_sub(start);
            if size == 0 || size > 16 * 1024 * 1024 {
                continue;
            }

            let mut buf = vec![0u8; size as usize];
            if file.seek(SeekFrom::Start(start)).is_err() || file.read_exact(&mut buf).is_err() {
                continue;
            }

            // Look for CInstance records: [obj_id (4 bytes)] [inst_id (4 bytes, 100000..900000)]
            for &b_id in battle_obj_ids {
                let target_bytes = b_id.to_le_bytes();
                let mut p = 0;
                while let Some(idx) = buf[p..].windows(4).position(|w| w == target_bytes) {
                    let absolute_offset = p + idx;
                    if absolute_offset + 8 <= buf.len() {
                        let inst_id = i32::from_le_bytes(buf[absolute_offset + 4..absolute_offset + 8].try_into().unwrap());
                        if (100_000..=999_999).contains(&inst_id) {
                            self.cached_battle_state = true;
                            return true;
                        }
                    }
                    p += idx + 4;
                }
            }
        }

        self.cached_battle_state = false;
        false
    }
}

// Detect current chapter from process working directory
fn detect_chapter(pid: u32) -> u32 {
    let cwd_link = format!("/proc/{pid}/cwd");
    if let Ok(target) = fs::read_link(cwd_link) {
        let path_str = target.to_string_lossy();
        for ch in 1..=7 {
            if path_str.contains(&format!("chapter{ch}")) {
                return ch;
            }
        }
    }

    0
}

// Find DELTARUNE process PID from /proc/
fn find_pid(_sys: &mut System) -> Option<u32> {
    if let Ok(entries) = fs::read_dir("/proc") {
        for entry in entries.flatten() {
            let fname = entry.file_name();
            if let Some(pid_str) = fname.to_str() {
                if let Ok(pid) = pid_str.parse::<u32>() {
                    let comm_path = format!("/proc/{pid}/comm");
                    if let Ok(comm) = fs::read_to_string(comm_path) {
                        let lower = comm.trim().to_lowercase();
                        if lower == "deltarune" || lower == "deltarune.exe" || lower.starts_with("deltarune") {
                            return Some(pid);
                        }
                    }
                }
            }
        }
    }

    None
}

fn print_status_box(state: &LiveGameState, state_desc: &str, details_desc: &str) {
    let stdout = io::stdout();
    let mut handle = stdout.lock();

    let room_id_str = state.room_id.map(|id| id.to_string()).unwrap_or_else(|| "Unknown".to_string());
    let raw_name = state.room_name.as_deref().unwrap_or("Unknown");

    let _ = writeln!(handle, "\n╭═══════════════════════════════════════════════════════════════╮");
    let _ = writeln!(handle, "║  Details       : {:<44} ║", details_desc);
    let _ = writeln!(handle, "║  State         : {:<44} ║", state_desc);
    let _ = writeln!(handle, "║  Room ID       : {:<44} ║", room_id_str);
    let _ = writeln!(handle, "║  Room Code     : {:<44} ║", raw_name);
    let _ = writeln!(handle, "╰═══════════════════════════════════════════════════════════════╯");
    let _ = handle.flush();
}

// Tray icon using standard StatusNotifierItem (compatible with Wayland, X11, GNOME, KDE, Hyprland, etc.)
struct DeltaTray {
    should_exit: Arc<AtomicBool>,
}

impl ksni::Tray for DeltaTray {
    fn id(&self) -> String {
        "delta-rpc".to_string()
    }

    fn title(&self) -> String {
        "deltaRPC".to_string()
    }

    fn icon_name(&self) -> String {
        "applications-games".to_string()
    }

    // Clicking / activating tray icon signals to exit
    fn activate(&mut self, _x: i32, _y: i32) {
        println!("\x1b[1;33m[!]\x1b[0m Tray icon activated. Exiting deltaRPC...");
        self.should_exit.store(true, Ordering::SeqCst);
    }
}

// Display error message box using system dialog
fn show_error_dialog(title: &str, message: &str) {
    #[cfg(target_os = "linux")]
    {
        // zenity first
        let zenity_res = Command::new("zenity")
            .arg("--error")
            .arg("--title")
            .arg(title)
            .arg("--text")
            .arg(message)
            .arg("--width=500")
            .status();

        if zenity_res.map(|s| s.success()).unwrap_or(false) {
            return;
        }

        // Try kdialog
        let kdialog_res = Command::new("kdialog")
            .arg("--title")
            .arg(title)
            .arg("--error")
            .arg(message)
            .status();

        if kdialog_res.map(|s| s.success()).unwrap_or(false) {
            return;
        }

        // Try notify-send desktop notification as fallback
        let notify_res = Command::new("notify-send")
            .arg("-u")
            .arg("critical")
            .arg(title)
            .arg(message)
            .status();

        if notify_res.map(|s| s.success()).unwrap_or(false) {
            return;
        }

        // Fallback to xmessage on basic X11 sessions
        let _ = Command::new("xmessage")
            .arg("-center")
            .arg(format!("{title}\n\n{message}"))
            .status();
    }

    #[cfg(target_os = "windows")]
    {
        use std::ffi::CString;
        // Basic Windows MessageBox fallback via powershell if native win32 api not linked
        let _ = Command::new("powershell")
            .arg("-Command")
            .arg(format!(
                "[System.Reflection.Assembly]::LoadWithPartialName('System.Windows.Forms'); [System.Windows.Forms.MessageBox]::Show('{}', '{}')",
                message.replace("'", "''"),
                title.replace("'", "''")
            ))
            .status();
    }
}

// Automatically copy error log to system clipboard (Wayland, X11, or Windows)
fn copy_to_clipboard(text: &str) {
    #[cfg(target_os = "linux")]
    {
        if let Ok(mut child) = Command::new("wl-copy")
            .stdin(Stdio::piped())
            .spawn()
        {
            if let Some(mut stdin) = child.stdin.take() {
                let _ = stdin.write_all(text.as_bytes());
            }
            if child.wait().map(|s| s.success()).unwrap_or(false) {
                return;
            }
        }

        if let Ok(mut child) = Command::new("xclip")
            .args(["-selection", "clipboard"])
            .stdin(Stdio::piped())
            .spawn()
        {
            if let Some(mut stdin) = child.stdin.take() {
                let _ = stdin.write_all(text.as_bytes());
            }
            if child.wait().map(|s| s.success()).unwrap_or(false) {
                return;
            }
        }

        if let Ok(mut child) = Command::new("xsel")
            .args(["--clipboard", "--input"])
            .stdin(Stdio::piped())
            .spawn()
        {
            if let Some(mut stdin) = child.stdin.take() {
                let _ = stdin.write_all(text.as_bytes());
            }
            let _ = child.wait();
        }
    }

    #[cfg(target_os = "windows")]
    {
        if let Ok(mut child) = Command::new("clip")
            .stdin(Stdio::piped())
            .spawn()
        {
            if let Some(mut stdin) = child.stdin.take() {
                let _ = stdin.write_all(text.as_bytes());
            }
            let _ = child.wait();
        }
    }
}

// Global crash handler to display full backtrace, copy log to clipboard, and exit
fn setup_crash_handler() {
    std::env::set_var("RUST_BACKTRACE", "full");

    panic::set_hook(Box::new(|info| {
        let is_term = io::stdout().is_terminal() || io::stderr().is_terminal();
        let backtrace = format!("{:?}", std::backtrace::Backtrace::capture());

        let plain_log = format!(
            "deltaRPC Crash Log\n\
             Error: {info}\n\n\
             Backtrace:\n{backtrace}\n\n\
             Report at: https://github.com/sungsoos/deltaRPC/issues"
        );

        // 1. Automatically copy the error log to the clipboard
        copy_to_clipboard(&plain_log);

        let console_msg = format!(
            "\n\x1b[1;31m====================================================================\x1b[0m\n\
\x1b[1;31m                      FATAL: deltaRPC CRASHED                       \x1b[0m\n\
\x1b[1;31m====================================================================\x1b[0m\n\
Error Information: {info}\n\n\
Full Backtrace:\n{backtrace}\n\
\x1b[1;33m--------------------------------------------------------------------\x1b[0m\n\
(Error log automatically copied to clipboard)\n\
Please report this issue with the log above at:\n\
  \x1b[1;36mhttps://github.com/sungsoos/deltaRPC/issues\x1b[0m\n\
\x1b[1;31m====================================================================\x1b[0m\n"
        );

        eprintln!("{console_msg}");

        if !is_term {
            let dialog_text = format!(
                "deltaRPC encountered a fatal error:\n\n{info}\n\n(The full error log has been automatically copied to your clipboard)\n\nPlease report this issue at:\nhttps://github.com/sungsoos/deltaRPC/issues"
            );
            show_error_dialog("deltaRPC Error", &dialog_text);
        }

        std::process::exit(1);
    }));
}

fn ctrl_del() {
    if !CrashOnCtrlDel {
        return;
    }

    thread::spawn(|| {
        println!("\x1b[1;33m[!]\x1b[0m CrashOnCtrlDel is ENABLED. Monitoring input devices for Ctrl + Delete...");

        if let Ok(entries) = fs::read_dir("/dev/input") {
            for entry in entries.flatten() {
                let path = entry.path();
                if let Some(fname) = path.file_name().and_then(|f| f.to_str()) {
                    if fname.starts_with("event") {
                        if let Ok(mut dev) = File::open(&path) {
                            thread::spawn(move || {
                                let mut buf = [0u8; 24];
                                let mut ctrl_pressed = false;

                                while dev.read_exact(&mut buf).is_ok() {
                                    let ev_type = u16::from_ne_bytes([buf[16], buf[17]]);
                                    let ev_code = u16::from_ne_bytes([buf[18], buf[19]]);
                                    let ev_val = i32::from_ne_bytes([buf[20], buf[21], buf[22], buf[23]]);

                                    if ev_type == 1 {
                                        if ev_code == 29 || ev_code == 97 {
                                            ctrl_pressed = ev_val > 0;
                                        }
                                        if ev_code == 111 && ev_val == 1 && ctrl_pressed {
                                            panic!("CrashOnCtrlDel!");
                                        }
                                    }
                                }
                            });
                        }
                    }
                }
            }
        }
    });
}

fn main() {
    setup_crash_handler();
    ctrl_del();

    println!("\x1b[1;36m[deltaRPC]\x1b[0m Initializing...");
    println!("\x1b[1;36m[deltaRPC]\x1b[0m System tray icon active (click tray icon to exit).");
    println!("\x1b[1;36m[deltaRPC]\x1b[0m Scanning for active DELTARUNE process...");

    let should_exit = Arc::new(AtomicBool::new(false));

    // Spawn tray icon background service
    use ksni::blocking::TrayMethods;
    let tray = DeltaTray {
        should_exit: Arc::clone(&should_exit),
    };
    let _tray_handle = tray.spawn();

    let mut sys = System::new();
    let mut last_detected_pid: Option<u32> = None;
    let mut cached_rooms: HashMap<i32, String> = HashMap::new();
    let mut cached_battle_obj_ids: Vec<i32> = Vec::new();
    let mut cached_chapter: u32 = 0;
    let mut inspector: Option<MemoryInspector> = None;
    let mut discord_client: Option<DiscordIpcClient> = None;
    let mut start_timestamp: Option<i64> = None;

    // Track last sent RPC presence to avoid Discord rate limiting
    let mut last_sent_details = String::new();
    let mut last_sent_state = String::new();
    let mut last_sent_small_icon = "";
    let mut last_rpc_update = Instant::now() - Duration::from_secs(60);

    while !should_exit.load(Ordering::SeqCst) {
        let game_pid = find_pid(&mut sys);

        match game_pid {
            Some(pid) => {
                let chapter = detect_chapter(pid);

                // Initialize start timestamp when game is first detected
                if start_timestamp.is_none() {
                    let now = SystemTime::now()
                        .duration_since(UNIX_EPOCH)
                        .map(|d| d.as_secs() as i64)
                        .unwrap_or(0);
                    start_timestamp = Some(now);
                }

                // Connect Discord IPC if not connected
                if discord_client.is_none() {
                    match DiscordIpcClient::new(DISCORD_APP_ID) {
                        Ok(mut ipc) => match ipc.connect() {
                            Ok(_) => {
                                println!("\x1b[1;32m[+]\x1b[0m Connected to Discord IPC.");
                                discord_client = Some(ipc);
                                last_sent_details.clear();
                                last_sent_state.clear();
                            }
                            Err(e) => {
                                eprintln!("\x1b[1;33m[!]\x1b[0m Waiting for Discord IPC: {e}");
                            }
                        },
                        Err(e) => {
                            eprintln!("\x1b[1;31m[-]\x1b[0m Failed to create Discord IPC client: {e}");
                        }
                    }
                }

                // Reload data.win room and battle definitions if chapter changed or first run
                if chapter != cached_chapter || cached_rooms.is_empty() {
                    let cwd_link = format!("/proc/{pid}/cwd");
                    if let Ok(cwd) = fs::read_link(cwd_link) {
                        let data_win_path = cwd.join("data.win");
                        cached_rooms = parse_rooms(&data_win_path);
                        cached_battle_obj_ids = parse_battle_obj(&data_win_path);
                        cached_chapter = chapter;
                        inspector = Some(MemoryInspector::new(pid));
                        println!(
                            "\x1b[1;32m[+]\x1b[0m Loaded {} rooms, {} battle objects from Chapter {chapter} data.win",
                            cached_rooms.len(),
                            cached_battle_obj_ids.len()
                        );
                    }
                }

                if last_detected_pid != Some(pid) {
                    last_detected_pid = Some(pid);
                    inspector = Some(MemoryInspector::new(pid));
                }

                let mem = inspector.as_mut().unwrap();

                let live_room_id = mem.read_room_id();
                let live_room_name = live_room_id.and_then(|id| cached_rooms.get(&id).cloned());

                let in_battle = mem.check_in_battle(&cached_battle_obj_ids);

                let state = LiveGameState {
                    chapter,
                    room_id: live_room_id,
                    room_name: live_room_name.clone(),
                    in_battle,
                };

                let details_desc = if chapter > 0 {
                    format!("Chapter {chapter}")
                } else {
                    "DELTARUNE".to_string()
                };

                let state_desc = get_state(live_room_name.as_deref(), in_battle, chapter);

                let small_image_key = match chapter {
                    1 => "icon_1",
                    2 => "icon_2",
                    3 => "icon_3",
                    4 => "icon_4",
                    5 => "icon_5",
                    _ => "icon_0",
                };

                let rpc_changed = details_desc != last_sent_details
                    || state_desc != last_sent_state
                    || small_image_key != last_sent_small_icon;

                let heartbeat_due = last_rpc_update.elapsed() >= Duration::from_secs(15);

                if (rpc_changed || heartbeat_due) && discord_client.is_some() {
                    if let Some(ref mut ipc) = discord_client {
                        let mut activity = Activity::new()
                            .details(&details_desc)
                            .state(&state_desc)
                            .assets(
                                Assets::new()
                                    .large_image("favicon")
                                    .large_text("DELTA RUNE")
                                    .small_image(small_image_key)
                                    .small_text(&details_desc),
                            );

                        if let Some(ts) = start_timestamp {
                            activity = activity.timestamps(Timestamps::new().start(ts));
                        }

                        match ipc.set_activity(activity) {
                            Ok(_) => {
                                last_sent_details = details_desc.clone();
                                last_sent_state = state_desc.clone();
                                last_sent_small_icon = small_image_key;
                                last_rpc_update = Instant::now();
                            }
                            Err(e) => {
                                eprintln!("\x1b[1;33m[!]\x1b[0m Discord activity update error: {e}");
                                let _ = ipc.close();
                                discord_client = None;
                            }
                        }
                    }
                }

                if rpc_changed {
                    print_status_box(&state, &state_desc, &details_desc);
                }
            }
            None => {
                if last_detected_pid.is_some() {
                    println!("\n\x1b[1;31m[-]\x1b[0m DELTARUNE process terminated. Clearing presence.");
                    if let Some(mut ipc) = discord_client.take() {
                        let _ = ipc.clear_activity();
                        let _ = ipc.close();
                    }
                    last_detected_pid = None;
                    cached_chapter = 0;
                    cached_rooms.clear();
                    cached_battle_obj_ids.clear();
                    inspector = None;
                    start_timestamp = None;
                    last_sent_details.clear();
                    last_sent_state.clear();
                }
                println!("[*] Waiting for DELTARUNE process...");
                let _ = io::stdout().flush();
            }
        }

        sleep(POLL_INTERVAL);
    }

    println!("[deltaRPC] Shutting down...");
    if let Some(mut ipc) = discord_client.take() {
        let _ = ipc.clear_activity();
        let _ = ipc.close();
    }
}
