#![windows_subsystem = "windows"]

use std::collections::HashMap;
use std::fs;
#[cfg(target_os = "linux")]
use std::fs::File;
use std::io::{self, Cursor, IsTerminal, Write};
#[cfg(target_os = "linux")]
use std::io::{Read, Seek, SeekFrom};
use std::panic;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread::{self, sleep};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use discord_rich_presence::activity::{Activity, Assets, Timestamps};
use discord_rich_presence::{DiscordIpc, DiscordIpcClient};
use sysinfo::System;

#[cfg(windows)]
use windows_sys::Win32::Foundation::{CloseHandle, HANDLE};
#[cfg(windows)]
use windows_sys::Win32::System::Memory::{
    VirtualQueryEx, MEMORY_BASIC_INFORMATION, MEM_COMMIT, PAGE_GUARD, PAGE_NOACCESS,
};
#[cfg(windows)]
use windows_sys::Win32::System::Threading::{
    OpenProcess, QueryFullProcessImageNameW, PROCESS_QUERY_INFORMATION, PROCESS_VM_READ,
};
#[cfg(windows)]
use windows_sys::Win32::UI::WindowsAndMessaging::{MessageBoxW, MB_ICONERROR, MB_OK};

const DISCORD_APP_ID: &str = "1553962630828531742"; // PLEASE CHANGE IT PLEASE PLEASE PLEASE
const POLL_INTERVAL: Duration = Duration::from_millis(1000);

#[allow(non_upper_case_globals)]
pub const CrashOnCtrlDel: bool = false;

#[derive(Debug, Clone, Default)]
pub struct LiveGameState {
    pub chapter: u32,
    pub room_id: Option<i32>,
    pub room_name: Option<String>,
}

// Room friendly name mapping (assets/data/room_names.jsonc)
const EMBEDDED_ROOM_NAMES_JSONC: &str = include_str!("../assets/data/room_names.jsonc");

// Strip single-line (//) and multi-line (/* */) comments from JSONC string
fn strip_jsonc_comments(jsonc: &str) -> String {
    let mut out = String::with_capacity(jsonc.len());
    let mut chars = jsonc.chars().peekable();
    let mut in_str = false;
    let mut escape = false;

    while let Some(c) = chars.next() {
        if escape {
            out.push(c);
            escape = false;
            continue;
        }
        if in_str {
            if c == '\\' {
                escape = true;
            } else if c == '"' {
                in_str = false;
            }
            out.push(c);
            continue;
        }

        if c == '"' {
            in_str = true;
            out.push(c);
        } else if c == '/' && chars.peek() == Some(&'/') {
            chars.next(); // consume second '/'
            for nc in chars.by_ref() {
                if nc == '\n' {
                    out.push('\n');
                    break;
                }
            }
        } else if c == '/' && chars.peek() == Some(&'*') {
            chars.next(); // consume '*'
            while let Some(nc) = chars.next() {
                if nc == '*' && chars.peek() == Some(&'/') {
                    chars.next(); // consume '/'
                    break;
                }
            }
        } else {
            out.push(c);
        }
    }

    out
}

// Load room name dictionary from JSONC: "<room_internal_name>": "<room_friendly_name>"
fn load_custom_room_names() -> HashMap<String, String> {
    let stripped = strip_jsonc_comments(EMBEDDED_ROOM_NAMES_JSONC);
    serde_json::from_str(&stripped).unwrap_or_default()
}

// Convert GameMaker room names to Discord state string
fn get_state(raw_room: Option<&str>, chapter: u32, custom_names: &HashMap<String, String>) -> String {
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

    if let Some(custom) = custom_names.get(raw) {
        if custom.starts_with("In ") {
            return custom.clone();
        }
        return match custom.as_str() {
            "Chapter Select" | "Title Screen" | "Game Over" | "Battle" => format!("In {custom}"),
            _ => format!("In {custom}"),
        };
    }

    let lower = raw.to_lowercase();
    if lower.contains("chapter_select") || lower.contains("place_chapter") {
        return "In Chapter Select".to_string();
    }
    if lower.contains("place_menu") || lower.contains("menu") || lower.contains("title") {
        return "In Title Screen".to_string();
    }
    if lower.contains("battle") {
        return "In Battle".to_string();
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

// Fallback: Parse room name map directly from data.win file if needed (e.g. mods or future chapters)
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

// Memory reader for DELTARUNE process
struct MemoryInspector {
    #[allow(dead_code)]
    pid: u32,
    #[cfg(target_os = "linux")]
    mem_file: Option<File>,
    #[cfg(windows)]
    handle: Option<HANDLE>,
    room_var_addr: Option<u64>,
}

#[cfg(windows)]
unsafe impl Send for MemoryInspector {}
#[cfg(windows)]
unsafe impl Sync for MemoryInspector {}

impl MemoryInspector {
    #[cfg(target_os = "linux")]
    fn new(pid: u32) -> Self {
        let mem_path = format!("/proc/{pid}/mem");
        let mem_file = File::open(mem_path).ok();
        Self {
            pid,
            mem_file,
            room_var_addr: None,
        }
    }

    #[cfg(windows)]
    fn new(pid: u32) -> Self {
        let handle = unsafe { OpenProcess(PROCESS_VM_READ | PROCESS_QUERY_INFORMATION, 0, pid) };
        let valid_handle = if handle == std::ptr::null_mut() { None } else { Some(handle) };
        Self {
            pid,
            handle: valid_handle,
            room_var_addr: None,
        }
    }

    #[cfg(target_os = "linux")]
    fn ensure_file(&mut self) -> Option<&mut File> {
        if self.mem_file.is_none() {
            let mem_path = format!("/proc/{}/mem", self.pid);
            self.mem_file = File::open(mem_path).ok();
        }
        self.mem_file.as_mut()
    }

    // Dynamically resolve GameMaker's global "room" integer address via the engine's built-in table
    #[cfg(target_os = "linux")]
    fn resolve_room_address(&mut self) -> Option<u64> {
        if let Some(addr) = self.room_var_addr {
            return Some(addr);
        }

        let maps_path = format!("/proc/{}/maps", self.pid);
        let maps_content = fs::read_to_string(maps_path).ok()?;
        let mem_file = self.ensure_file()?;

        let mut str_candidates: Vec<u64> = Vec::new();

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
                        // GameMaker code functions are non-null 64-bit pointers
                        if fn_ptr > 0x10000 && fn_ptr < 0x7fff_ffff_ffff {
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

    #[cfg(windows)]
    fn resolve_room_address(&mut self) -> Option<u64> {
        if let Some(addr) = self.room_var_addr {
            return Some(addr);
        }

        let handle = self.handle?;
        let mut regions: Vec<(u64, usize)> = Vec::new();
        let mut cur_addr: usize = 0;

        unsafe {
            let mut mbi: MEMORY_BASIC_INFORMATION = std::mem::zeroed();
            while VirtualQueryEx(
                handle,
                cur_addr as *const _,
                &mut mbi,
                std::mem::size_of::<MEMORY_BASIC_INFORMATION>(),
            ) != 0
            {
                if mbi.State == MEM_COMMIT
                    && (mbi.Protect & (PAGE_GUARD | PAGE_NOACCESS)) == 0
                    && mbi.RegionSize > 0
                    && mbi.RegionSize <= 32 * 1024 * 1024
                {
                    regions.push((mbi.BaseAddress as u64, mbi.RegionSize));
                }

                let next = (mbi.BaseAddress as usize).checked_add(mbi.RegionSize);
                match next {
                    Some(n) if n > cur_addr => cur_addr = n,
                    _ => break,
                }
            }
        }

        let mut str_candidates: Vec<u64> = Vec::new();

        for &(base, size) in &regions {
            if size > 16 * 1024 * 1024 {
                continue;
            }
            let mut buf = vec![0u8; size];
            let mut bytes_read = 0;
            let success = unsafe {
                windows_sys::Win32::System::Diagnostics::Debug::ReadProcessMemory(
                    handle,
                    base as *const _,
                    buf.as_mut_ptr() as *mut _,
                    size,
                    &mut bytes_read,
                )
            };
            if success == 0 || bytes_read == 0 {
                continue;
            }
            buf.truncate(bytes_read);

            let mut p = 0;
            while let Some(idx) = buf[p..].windows(8).position(|w| w == b"\x00room\x00\x00\x00") {
                str_candidates.push(base + (p + idx + 1) as u64);
                p += idx + 8;
            }
        }

        for s_addr in str_candidates {
            let s_bytes = s_addr.to_le_bytes();

            for &(base, size) in &regions {
                let mut buf = vec![0u8; size];
                let mut bytes_read = 0;
                let success = unsafe {
                    windows_sys::Win32::System::Diagnostics::Debug::ReadProcessMemory(
                        handle,
                        base as *const _,
                        buf.as_mut_ptr() as *mut _,
                        size,
                        &mut bytes_read,
                    )
                };
                if success == 0 || bytes_read == 0 {
                    continue;
                }
                buf.truncate(bytes_read);

                let mut idx = 0;
                while let Some(p) = buf[idx..].windows(8).position(|w| w == s_bytes) {
                    let entry_offset = idx + p;
                    if entry_offset + 16 <= buf.len() {
                        let fn_ptr = u64::from_le_bytes(buf[entry_offset + 8..entry_offset + 16].try_into().unwrap());
                        // GameMaker code functions are non-null 64-bit pointers (handles ASLR)
                        if fn_ptr > 0x10000 && fn_ptr < 0x7fff_ffff_ffff {
                            let mut fn_bytes = [0u8; 24];
                            let mut fn_read = 0;
                            let fn_success = unsafe {
                                windows_sys::Win32::System::Diagnostics::Debug::ReadProcessMemory(
                                    handle,
                                    fn_ptr as *const _,
                                    fn_bytes.as_mut_ptr() as *mut _,
                                    fn_bytes.len(),
                                    &mut fn_read,
                                )
                            };
                            if fn_success != 0 && fn_read == 24 {
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

    #[cfg(target_os = "linux")]
    fn read_room_id(&mut self) -> Option<i32> {
        let addr = self.resolve_room_address()?;
        let file = self.ensure_file()?;
        file.seek(SeekFrom::Start(addr)).ok()?;
        let mut buf = [0u8; 4];
        file.read_exact(&mut buf).ok()?;
        Some(i32::from_le_bytes(buf))
    }

    #[cfg(windows)]
    fn read_room_id(&mut self) -> Option<i32> {
        let addr = self.resolve_room_address()?;
        let handle = self.handle?;
        let mut buf = [0u8; 4];
        let mut bytes_read = 0;
        let success = unsafe {
            windows_sys::Win32::System::Diagnostics::Debug::ReadProcessMemory(
                handle,
                addr as *const _,
                buf.as_mut_ptr() as *mut _,
                4,
                &mut bytes_read,
            )
        };
        if success != 0 && bytes_read == 4 {
            Some(i32::from_le_bytes(buf))
        } else {
            None
        }
    }
}

#[cfg(windows)]
impl Drop for MemoryInspector {
    fn drop(&mut self) {
        if let Some(h) = self.handle {
            unsafe {
                CloseHandle(h);
            }
        }
    }
}

// Detect current chapter from process working directory or executable path
fn detect_chapter(pid: u32, sys: &mut System) -> u32 {
    #[cfg(target_os = "linux")]
    {
        let _ = sys;
        let cwd_link = format!("/proc/{pid}/cwd");
        if let Ok(target) = fs::read_link(cwd_link) {
            let path_str = target.to_string_lossy();
            for ch in 1..=7 {
                if path_str.contains(&format!("chapter{ch}")) {
                    return ch;
                }
            }
        }
    }

    #[cfg(windows)]
    {
        if let Some(exe_path) = get_process_exe_path(pid, sys) {
            let path_str = exe_path.to_string_lossy().to_lowercase();
            for ch in 1..=7 {
                if path_str.contains(&format!("chapter{ch}")) {
                    return ch;
                }
            }
        }
    }

    0
}

#[cfg(windows)]
fn get_process_exe_path(pid: u32, sys: &System) -> Option<PathBuf> {
    let handle = unsafe { OpenProcess(PROCESS_QUERY_INFORMATION | PROCESS_VM_READ, 0, pid) };
    if handle != std::ptr::null_mut() {
        let mut buf = [0u16; 1024];
        let mut size = buf.len() as u32;
        let len = unsafe {
            QueryFullProcessImageNameW(
                handle,
                0,
                buf.as_mut_ptr(),
                &mut size,
            )
        };
        unsafe { CloseHandle(handle) };
        if len != 0 && size > 0 {
            use std::ffi::OsString;
            use std::os::windows::ffi::OsStringExt;
            let os_str = OsString::from_wide(&buf[..size as usize]);
            return Some(PathBuf::from(os_str));
        }
    }

    for (proc_pid, proc) in sys.processes() {
        if proc_pid.as_u32() == pid {
            if let Some(exe) = proc.exe() {
                return Some(exe.to_path_buf());
            }
        }
    }

    None
}

// Locate data.win file path for running DELTARUNE process
fn get_data_win_path(pid: u32, sys: &System) -> Option<PathBuf> {
    #[cfg(target_os = "linux")]
    {
        let _ = sys;
        let cwd_link = format!("/proc/{pid}/cwd");
        if let Ok(cwd) = fs::read_link(cwd_link) {
            let data_win = cwd.join("data.win");
            if data_win.exists() {
                return Some(data_win);
            }
        }
    }

    #[cfg(windows)]
    {
        if let Some(exe) = get_process_exe_path(pid, sys) {
            if let Some(dir) = exe.parent() {
                let data_win = dir.join("data.win");
                if data_win.exists() {
                    return Some(data_win);
                }
            }
        }
    }

    None
}

// Find DELTARUNE process PID
fn find_pid(sys: &mut System) -> Option<u32> {
    #[cfg(target_os = "linux")]
    {
        let _ = sys;
        let mut fallback_pid = None;
        if let Ok(entries) = fs::read_dir("/proc") {
            for entry in entries.flatten() {
                let fname = entry.file_name();
                if let Some(pid_str) = fname.to_str() {
                    if let Ok(pid) = pid_str.parse::<u32>() {
                        let comm_path = format!("/proc/{pid}/comm");
                        if let Ok(comm) = fs::read_to_string(comm_path) {
                            let lower = comm.trim().to_lowercase();
                            if lower == "deltarune" || lower == "deltarune.exe" || lower.starts_with("deltarune") {
                                // Prefer active chapter process if launched
                                let cwd_link = format!("/proc/{pid}/cwd");
                                if let Ok(cwd) = fs::read_link(cwd_link) {
                                    let cwd_str = cwd.to_string_lossy().to_lowercase();
                                    if cwd_str.contains("chapter") {
                                        return Some(pid);
                                    }
                                }
                                if fallback_pid.is_none() {
                                    fallback_pid = Some(pid);
                                }
                            }
                        }
                    }
                }
            }
        }
        return fallback_pid;
    }

    #[cfg(windows)]
    {
        sys.refresh_processes(sysinfo::ProcessesToUpdate::All, true);
        let candidate_pids: Vec<u32> = sys
            .processes()
            .iter()
            .filter_map(|(pid, proc)| {
                let name = proc.name().to_string_lossy().to_lowercase();
                if name == "deltarune.exe" || name == "deltarune" {
                    Some(pid.as_u32())
                } else {
                    None
                }
            })
            .collect();

        let mut fallback_pid = None;
        for pid in candidate_pids {
            // Query process path to distinguish chapter process from launcher
            if let Some(exe_path) = get_process_exe_path(pid, sys) {
                let path_str = exe_path.to_string_lossy().to_lowercase();
                if path_str.contains("chapter") {
                    return Some(pid);
                }
            }
            if fallback_pid.is_none() {
                fallback_pid = Some(pid);
            }
        }
        return fallback_pid;
    }

    #[allow(unreachable_code)]
    None
}


fn print_status_box(state: &LiveGameState, state_desc: &str, details_desc: &str) {
    let stdout = io::stdout();
    let mut handle = stdout.lock();

    let room_id_str = state.room_id.map(|id| id.to_string()).unwrap_or_else(|| "Unknown".to_string());
    let raw_name = state.room_name.as_deref().unwrap_or("Unknown");

    let _ = writeln!(handle, "\n╭───────────────────────────────────────────────────────────────╮");
    let _ = writeln!(handle, "│  Details       : {:<44} │", details_desc);
    let _ = writeln!(handle, "│  State         : {:<44} │", state_desc);
    let _ = writeln!(handle, "│  Room ID       : {:<44} │", room_id_str);
    let _ = writeln!(handle, "│  Room Code     : {:<44} │", raw_name);
    let _ = writeln!(handle, "╰───────────────────────────────────────────────────────────────╯");
    let _ = handle.flush();
}

// Embedded application icon: assets/img/app/icon.png
const APP_ICON_PNG: &[u8] = include_bytes!("../assets/img/app/icon.png");

// Ensure embedded icon is written to a reliable cache path for hosts using icon_theme_path
#[cfg(target_os = "linux")]
fn ensure_icon_cache() -> Option<String> {
    let base = std::env::var("XDG_CACHE_HOME")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|_| {
            let home = std::env::var("HOME").unwrap_or_else(|_| ".".to_string());
            std::path::PathBuf::from(home).join(".cache")
        });
    let icon_dir = base.join("delta-rpc").join("icons");
    let _ = fs::create_dir_all(&icon_dir);
    let icon_file = icon_dir.join("delta-rpc.png");
    if !icon_file.exists() {
        let _ = fs::write(&icon_file, APP_ICON_PNG);
    }
    icon_dir.to_str().map(|s| s.to_string())
}

#[cfg(target_os = "linux")]
fn load_tray_icon() -> Option<ksni::Icon> {
    let decoder = png::Decoder::new(Cursor::new(APP_ICON_PNG));
    let mut reader = decoder.read_info().ok()?;
    let mut buf = vec![0; reader.output_buffer_size()?];
    let info = reader.next_frame(&mut buf).ok()?;
    let bytes = &buf[..info.buffer_size()];

    let mut argb_data = Vec::with_capacity((info.width * info.height * 4) as usize);

    match info.color_type {
        png::ColorType::Rgba => {
            for chunk in bytes.chunks_exact(4) {
                let r = chunk[0];
                let g = chunk[1];
                let b = chunk[2];
                let a = chunk[3];
                // SNI protocol expects ARGB32 format in network byte order: [A, R, G, B]
                argb_data.extend_from_slice(&[a, r, g, b]);
            }
        }
        png::ColorType::Rgb => {
            for chunk in bytes.chunks_exact(3) {
                let r = chunk[0];
                let g = chunk[1];
                let b = chunk[2];
                let a = 255;
                argb_data.extend_from_slice(&[a, r, g, b]);
            }
        }
        _ => return None,
    }

    Some(ksni::Icon {
        width: info.width as i32,
        height: info.height as i32,
        data: argb_data,
    })
}

// Tray icon using standard StatusNotifierItem (compatible with Wayland, X11, GNOME, KDE, Hyprland, etc.)
#[cfg(target_os = "linux")]
struct DeltaTray {
    should_exit: Arc<AtomicBool>,
    icon_theme_dir: String,
}

#[cfg(target_os = "linux")]
impl ksni::Tray for DeltaTray {
    fn id(&self) -> String {
        "delta-rpc".to_string()
    }

    fn title(&self) -> String {
        "deltaRPC".to_string()
    }

    fn category(&self) -> ksni::Category {
        ksni::Category::ApplicationStatus
    }

    fn status(&self) -> ksni::Status {
        ksni::Status::Active
    }

    fn icon_name(&self) -> String {
        "delta-rpc".to_string()
    }

    fn icon_theme_path(&self) -> String {
        self.icon_theme_dir.clone()
    }

    fn icon_pixmap(&self) -> Vec<ksni::Icon> {
        match load_tray_icon() {
            Some(icon) => vec![icon],
            None => Vec::new(),
        }
    }

    fn menu(&self) -> Vec<ksni::MenuItem<Self>> {
        use ksni::menu::StandardItem;
        vec![
            StandardItem {
                label: "Exit deltaRPC".to_string(),
                activate: Box::new(|tray: &mut Self| {
                    tray.should_exit.store(true, Ordering::SeqCst);
                }),
                ..Default::default()
            }
            .into(),
        ]
    }

    // Clicking / activating tray icon signals to exit
    fn activate(&mut self, _x: i32, _y: i32) {
        println!("\x1b[1;33m[!]\x1b[0m Tray icon activated. Exiting deltaRPC...");
        self.should_exit.store(true, Ordering::SeqCst);
    }
}

// Load RGBA icon for Windows tray-icon crate
#[cfg(windows)]
fn load_win_tray_icon() -> Option<tray_icon::Icon> {
    let decoder = png::Decoder::new(Cursor::new(APP_ICON_PNG));
    let mut reader = decoder.read_info().ok()?;
    let mut buf = vec![0; reader.output_buffer_size()?];
    let info = reader.next_frame(&mut buf).ok()?;
    let bytes = &buf[..info.buffer_size()];

    let rgba_data = match info.color_type {
        png::ColorType::Rgba => bytes.to_vec(),
        png::ColorType::Rgb => {
            let mut rgba = Vec::with_capacity((info.width * info.height * 4) as usize);
            for chunk in bytes.chunks_exact(3) {
                rgba.extend_from_slice(&[chunk[0], chunk[1], chunk[2], 255]);
            }
            rgba
        }
        _ => return None,
    };

    tray_icon::Icon::from_rgba(rgba_data, info.width, info.height).ok()
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

    #[cfg(windows)]
    {
        use std::os::windows::ffi::OsStrExt;
        let wide_title: Vec<u16> = std::ffi::OsStr::new(title).encode_wide().chain(std::iter::once(0)).collect();
        let wide_msg: Vec<u16> = std::ffi::OsStr::new(message).encode_wide().chain(std::iter::once(0)).collect();
        unsafe {
            MessageBoxW(std::ptr::null_mut(), wide_msg.as_ptr(), wide_title.as_ptr(), MB_OK | MB_ICONERROR);
        }
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

    #[cfg(target_os = "linux")]
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
    #[cfg(target_os = "linux")]
    {
        use ksni::blocking::TrayMethods;
        let icon_dir = ensure_icon_cache().unwrap_or_default();
        let tray = DeltaTray {
            should_exit: Arc::clone(&should_exit),
            icon_theme_dir: icon_dir,
        };
        match tray.spawn() {
            Ok(_handle) => {
                println!("\x1b[1;32m[+]\x1b[0m System tray icon registered successfully.");
            }
            Err(e) => {
                eprintln!("\x1b[1;33m[!]\x1b[0m System tray initialization note: {e}");
            }
        }
    }

    #[cfg(windows)]
    {
        let exit_flag = Arc::clone(&should_exit);
        thread::spawn(move || {
            let icon = load_win_tray_icon();
            let mut builder = tray_icon::TrayIconBuilder::new()
                .with_tooltip("deltaRPC");

            if let Some(i) = icon {
                builder = builder.with_icon(i);
            }

            let tray = match builder.build() {
                Ok(t) => {
                    println!("\x1b[1;32m[+]\x1b[0m System tray icon registered successfully.");
                    Some(t)
                }
                Err(e) => {
                    eprintln!("\x1b[1;33m[!]\x1b[0m System tray initialization note: {e}");
                    None
                }
            };

            let tray_channel = tray_icon::TrayIconEvent::receiver();
            while !exit_flag.load(Ordering::SeqCst) {
                unsafe {
                    let mut msg = std::mem::zeroed();
                    while windows_sys::Win32::UI::WindowsAndMessaging::PeekMessageW(
                        &mut msg,
                        std::ptr::null_mut(),
                        0,
                        0,
                        windows_sys::Win32::UI::WindowsAndMessaging::PM_REMOVE,
                    ) != 0
                    {
                        windows_sys::Win32::UI::WindowsAndMessaging::TranslateMessage(&msg);
                        windows_sys::Win32::UI::WindowsAndMessaging::DispatchMessageW(&msg);
                    }
                }


                while let Ok(event) = tray_channel.try_recv() {
                    match event {
                        tray_icon::TrayIconEvent::Click { button: tray_icon::MouseButton::Left, .. }
                        | tray_icon::TrayIconEvent::DoubleClick { .. } => {
                            println!("\x1b[1;33m[!]\x1b[0m Tray icon activated. Exiting deltaRPC...");
                            exit_flag.store(true, Ordering::SeqCst);
                            break;
                        }
                        _ => {}
                    }
                }

                sleep(Duration::from_millis(50));
            }

            drop(tray);
        });
    }

    let mut sys = System::new();
    let custom_room_names = load_custom_room_names();
    println!("\x1b[1;32m[+]\x1b[0m Loaded {} custom room name mappings.", custom_room_names.len());
    let mut last_detected_pid: Option<u32> = None;
    let mut cached_rooms: HashMap<i32, String> = HashMap::new();
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
                let chapter = detect_chapter(pid, &mut sys);

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

                // If process changed or chapter changed, recreate memory inspector and reload room definitions
                if last_detected_pid != Some(pid) || chapter != cached_chapter || cached_rooms.is_empty() {
                    let mut rooms = HashMap::new();
                    if let Some(data_win_path) = get_data_win_path(pid, &mut sys) {
                        rooms = parse_rooms(&data_win_path);
                    }
                    println!(
                        "\x1b[1;32m[+]\x1b[0m Attached to DELTARUNE (PID {pid}, Chapter {chapter}, {} rooms)",
                        rooms.len()
                    );
                    cached_chapter = chapter;
                    cached_rooms = rooms;
                    last_detected_pid = Some(pid);
                    inspector = Some(MemoryInspector::new(pid));
                }

                let mem = inspector.as_mut().unwrap();

                let live_room_id = mem.read_room_id();
                let live_room_name = live_room_id.and_then(|id| cached_rooms.get(&id).cloned());

                let state = LiveGameState {
                    chapter,
                    room_id: live_room_id,
                    room_name: live_room_name.clone(),
                };

                let details_desc = if chapter > 0 {
                    format!("Chapter {chapter}")
                } else {
                    "DELTARUNE".to_string()
                };

                let state_desc = get_state(live_room_name.as_deref(), chapter, &custom_room_names);

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
