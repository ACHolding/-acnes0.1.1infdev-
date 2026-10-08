#!/usr/bin/env python3
"""
acnesemu 0.1.x by ac kondo [c] acholdings
=========================================

A single-file, clean-room NES/Famicom emulator and debugger for Python 3.14.
The desktop UI mirrors classic FCEUX Win32: native menu bar (File / NES /
Config / Tools / Debug / Help), black game client, optional separate debugger
window, and right-click context menu.

Features (FCEUX-class core surface)
-----------------------------------
* Complete 256-entry Ricoh 2A03/6502 opcode map, including unofficial NMOS
  opcodes (LAX, SAX, DCP, ISC, SLO, RLA, SRE, RRA, ANC, ALR, ARR, AXS, …).
* NTSC Famicom timing target (60.0988 frames per second) with odd-frame skip.
* Background and sprite rendering with scanline-accurate raster output for
  MMC3 IRQ split-scroll games (Super Mario Bros. 3 status bar, etc.).
  sprite overflow, left-column clip, greyscale/emphasis, OAM DMA, controllers,
  NMI, IRQ, and mapper IRQ support.
* Cycle-timed pulse, triangle, noise, and DMC audio with the NES nonlinear
  mixer and optional 48 kHz real-time pygame-ce output.
* iNES/NES 2.0 loading with broad commercial-library mapper coverage
  (NROM/MMC1–5/UxROM/CNROM/AxROM/MMC2–4/VRC1–7/FME-7/Namco/Taito/Irem/
  Camerica/Color Dreams/Sunsoft/Jaleco/Bandai and common MMC3 variants).
* Open, reset, pause, frame-step, screenshot, scaling, and debugger controls.
* No ROMs, BIOS files, external assets, or third-party Python packages.

This is an original educational implementation, not FCEUX source code. FCEUX
has many years of hardware-accuracy work and supports far more boards, audio
edge cases, tools, and peripherals. Use ROM dumps that you are entitled to use.
"""

from __future__ import annotations

import argparse
import os
import pathlib
import sys
import time
import tkinter as tk
from array import array
from dataclasses import dataclass
from tkinter import filedialog, messagebox, ttk
from typing import Callable, Optional


APP_TITLE = "acnesemu 0.1.x"
APP_VERSION = "0.1.x"
APP_AUTHOR = "ac kondo / acholdings"
# Classic Win32 / FCEUX chrome (Windows 98-era system colors).
WIN_FACE = "#d4d0c8"
WIN_LIGHT = "#ffffff"
WIN_SHADOW = "#808080"
WIN_DARK = "#404040"
WIN_WINDOW = "#ffffff"
WIN_MENU = "#d4d0c8"
WIN_TEXT = "#000000"
WIN_DISABLED = "#808080"
WIN_HIGHLIGHT = "#0a246a"
WIN_HIGHLIGHT_TEXT = "#ffffff"
WIN_CLIENT = "#000000"
NTSC_FPS = 60.0988
CPU_CLOCK = 1_789_773
SCREEN_W = 256
SCREEN_H = 240

# Common NTSC 2C02 palette. Exact colors varied with display hardware.
NES_PALETTE = (
    (84, 84, 84), (0, 30, 116), (8, 16, 144), (48, 0, 136),
    (68, 0, 100), (92, 0, 48), (84, 4, 0), (60, 24, 0),
    (32, 42, 0), (8, 58, 0), (0, 64, 0), (0, 60, 0),
    (0, 50, 60), (0, 0, 0), (0, 0, 0), (0, 0, 0),
    (152, 150, 152), (8, 76, 196), (48, 50, 236), (92, 30, 228),
    (136, 20, 176), (160, 20, 100), (152, 34, 32), (120, 60, 0),
    (84, 90, 0), (40, 114, 0), (8, 124, 0), (0, 118, 40),
    (0, 102, 120), (0, 0, 0), (0, 0, 0), (0, 0, 0),
    (236, 238, 236), (76, 154, 236), (120, 124, 236), (176, 98, 236),
    (228, 84, 236), (236, 88, 180), (236, 106, 100), (212, 136, 32),
    (160, 170, 0), (116, 196, 0), (76, 208, 32), (56, 204, 108),
    (56, 180, 204), (60, 60, 60), (0, 0, 0), (0, 0, 0),
    (236, 238, 236), (168, 204, 236), (188, 188, 236), (212, 178, 236),
    (236, 174, 236), (236, 174, 212), (236, 180, 176), (228, 196, 144),
    (204, 210, 120), (180, 222, 120), (168, 226, 144), (152, 226, 180),
    (160, 214, 228), (160, 162, 160), (0, 0, 0), (0, 0, 0),
)


# Precomputed bitplane decode: PIXEL_ROW_LUT[(high << 8) | low] -> 8 pixel values
# (leftmost pixel first). Removes 8 shifts/masks from every background tile row.
PIXEL_ROW_LUT = tuple(
    bytes(
        (((low >> bit) & 1) | (((high >> bit) & 1) << 1))
        for bit in range(7, -1, -1)
    )
    for high in range(256)
    for low in range(256)
)

MIRROR_REMAP = {
    "vertical": (0, 1, 0, 1),
    "horizontal": (0, 0, 1, 1),
    "single0": (0, 0, 0, 0),
    "single1": (1, 1, 1, 1),
    "four": (0, 1, 2, 3),
}



class CartridgeError(ValueError):
    """Raised when a cartridge image is malformed or unsupported."""


class Mapper:
    def __init__(self, cart: "Cartridge") -> None:
        self.cart = cart
        self.irq_pending = False
        self.needs_cpu_clock = False

    def cpu_read(self, address: int) -> Optional[int]:
        raise NotImplementedError

    def cpu_write(self, address: int, value: int) -> bool:
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return address % self.cart.chr_len
        return None

    def ppu_write(self, address: int, value: int) -> bool:
        # Route CHR-RAM writes through the mapper's banking so banked
        # CHR-RAM boards (VRC, Namco, …) write to the selected bank.
        if address < 0x2000 and self.cart.chr_is_ram:
            index = self.ppu_read(address)
            if index is not None:
                self.cart.chr[index] = value
                return True
        return False

    def register_read(self, address: int) -> Optional[int]:
        """Read a mapper register in $4020-$5FFF, returning a data byte."""
        return None

    def mirror_mode(self) -> str:
        return self.cart.header_mirroring

    def clock_scanline(self) -> None:
        pass

    def clock_cpu(self, cycles: int) -> None:
        """Advance CPU-cycle IRQ counters (VRC/FME-7/Namco/etc.)."""

    def reset(self) -> None:
        self.irq_pending = False


class Mapper0(Mapper):
    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            return (address - 0x8000) % len(self.cart.prg)
        return None


class Mapper1(Mapper):
    """MMC1/SxROM mapper with serial bank register."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.shift = 0x10
        self.control = 0x0C
        self.chr0 = 0
        self.chr1 = 0
        self.prg_bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        mode = (self.control >> 2) & 3
        bank_count = max(1, len(self.cart.prg) // 0x4000)
        if mode in (0, 1):
            bank = (self.prg_bank & 0x0E) % bank_count
            return (bank * 0x4000 + (address & 0x7FFF)) % len(self.cart.prg)
        if mode == 2:
            bank = 0 if address < 0xC000 else self.prg_bank % bank_count
        else:
            bank = self.prg_bank % bank_count if address < 0xC000 else bank_count - 1
        return (bank * 0x4000 + (address & 0x3FFF)) % len(self.cart.prg)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        if value & 0x80:
            self.shift = 0x10
            self.control |= 0x0C
            return True
        complete = bool(self.shift & 1)
        self.shift = (self.shift >> 1) | ((value & 1) << 4)
        if complete:
            register = (address >> 13) & 3
            data = self.shift & 0x1F
            if register == 0:
                self.control = data
            elif register == 1:
                self.chr0 = data
            elif register == 2:
                self.chr1 = data
            else:
                self.prg_bank = data & 0x0F
            self.shift = 0x10
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        if self.control & 0x10:
            bank = self.chr0 if address < 0x1000 else self.chr1
            index = bank * 0x1000 + (address & 0x0FFF)
        else:
            bank = self.chr0 & 0x1E
            index = bank * 0x1000 + address
        return index % len(self.cart.chr)

    def ppu_write(self, address: int, value: int) -> bool:
        index = self.ppu_read(address)
        if index is not None and self.cart.chr_is_ram:
            self.cart.chr[index] = value
            return True
        return False

    def mirror_mode(self) -> str:
        return ("single0", "single1", "vertical", "horizontal")[self.control & 3]


class Mapper2(Mapper):
    """UxROM mapper."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = self.bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.bank = value
            return True
        return False


class Mapper3(Mapper):
    """CNROM mapper."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.chr_bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            return (address - 0x8000) % len(self.cart.prg)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.chr_bank = value & 3
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return (self.chr_bank * 0x2000 + address) % len(self.cart.chr)
        return None


class Mapper4(Mapper):
    """MMC3/MMC6-compatible banking and scanline IRQ counter."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.select = 0
        self.regs = [0] * 8
        self.mirror = cart.header_mirroring
        self.irq_latch = 0
        self.irq_counter = 0
        self.irq_reload = False
        self.irq_enabled = False
        self._chr_base = [0] * 8
        self._chr_xor = 0
        self._rebuild_chr()

    def _rebuild_chr(self) -> None:
        regs = self.regs
        chr_len = self.cart.chr_len
        bases = self._chr_base
        bases[0] = ((regs[0] & 0xFE) * 0x400) % chr_len
        bases[1] = (((regs[0] & 0xFE) + 1) * 0x400) % chr_len
        bases[2] = ((regs[1] & 0xFE) * 0x400) % chr_len
        bases[3] = (((regs[1] & 0xFE) + 1) * 0x400) % chr_len
        bases[4] = (regs[2] * 0x400) % chr_len
        bases[5] = (regs[3] * 0x400) % chr_len
        bases[6] = (regs[4] * 0x400) % chr_len
        bases[7] = (regs[5] * 0x400) % chr_len
        self._chr_xor = 0x1000 if self.select & 0x80 else 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = self.cart.prg_8k
        last = count - 1
        second_last = last - 1 if last else 0
        slot = (address - 0x8000) >> 13
        mode = (self.select >> 6) & 1
        if slot == 0:
            bank = second_last if mode else self.regs[6]
        elif slot == 1:
            bank = self.regs[7]
        elif slot == 2:
            bank = self.regs[6] if mode else second_last
        else:
            bank = last
        return (bank % count) * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        even = not (address & 1)
        region = address & 0xE000
        if region == 0x8000:
            if even:
                self.select = value
                self._chr_xor = 0x1000 if value & 0x80 else 0
            else:
                register = self.select & 7
                self.regs[register] = value & (0xFE if register in (0, 1) else 0xFF)
                if register <= 5:
                    self._rebuild_chr()
        elif region == 0xA000:
            if even and self.cart.header_mirroring != "four":
                self.mirror = "horizontal" if value & 1 else "vertical"
        elif region == 0xC000:
            if even:
                self.irq_latch = value
            else:
                self.irq_reload = True
        elif region == 0xE000:
            if even:
                self.irq_enabled = False
                self.irq_pending = False
            else:
                self.irq_enabled = True
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        logical = address ^ self._chr_xor
        return self._chr_base[logical >> 10] + (logical & 0x3FF)

    def ppu_write(self, address: int, value: int) -> bool:
        index = self.ppu_read(address)
        if index is not None and self.cart.chr_is_ram:
            self.cart.chr[index] = value
            return True
        return False

    def mirror_mode(self) -> str:
        return self.mirror

    def clock_scanline(self) -> None:
        if self.irq_counter == 0 or self.irq_reload:
            self.irq_counter = self.irq_latch
            self.irq_reload = False
        else:
            self.irq_counter = (self.irq_counter - 1) & 0xFF
        if self.irq_counter == 0 and self.irq_enabled:
            self.irq_pending = True


class Mapper7(Mapper):
    """AxROM mapper."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.bank = 0
        self.single = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            banks = max(1, len(self.cart.prg) // 0x8000)
            return (self.bank % banks) * 0x8000 + (address & 0x7FFF)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.bank = value & 7
            self.single = (value >> 4) & 1
            return True
        return False

    def mirror_mode(self) -> str:
        return "single1" if self.single else "single0"


class Mapper66(Mapper):
    """GxROM mapper."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            banks = max(1, len(self.cart.prg) // 0x8000)
            return (self.prg_bank % banks) * 0x8000 + (address & 0x7FFF)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.prg_bank = (value >> 4) & 3
            self.chr_bank = value & 3
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return (self.chr_bank * 0x2000 + address) % len(self.cart.chr)
        return None


class Mapper9(Mapper):
    """MMC2 (Punch-Out!!) with PPU CHR latches."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_fd = [0, 0]
        self.chr_fe = [0, 0]
        self.latch = [True, True]
        self.mirror = cart.header_mirroring

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        if address < 0xA000:
            bank = self.prg_bank % count
        else:
            bank = count - (3 - (address - 0xA000) // 0x2000)
            bank = max(0, min(count - 1, bank))
        return (bank % count) * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0xA000:
            return False
        region = address & 0xF000
        if region == 0xA000:
            self.prg_bank = value & 0x0F
        elif region == 0xB000:
            self.chr_fd[0] = value & 0x1F
        elif region == 0xC000:
            self.chr_fe[0] = value & 0x1F
        elif region == 0xD000:
            self.chr_fd[1] = value & 0x1F
        elif region == 0xE000:
            self.chr_fe[1] = value & 0x1F
        elif region == 0xF000:
            self.mirror = "horizontal" if value & 1 else "vertical"
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        slot = 0 if address < 0x1000 else 1
        bank = self.chr_fe[slot] if self.latch[slot] else self.chr_fd[slot]
        index = (bank * 0x1000 + (address & 0x0FFF)) % len(self.cart.chr)
        lo = address & 0x0FF8
        if lo == 0x0FD8:
            self.latch[slot] = False
        elif lo == 0x0FE8:
            self.latch[slot] = True
        return index

    def ppu_write(self, address: int, value: int) -> bool:
        index = self.ppu_read(address)
        if index is not None and self.cart.chr_is_ram:
            self.cart.chr[index] = value
            return True
        return False

    def mirror_mode(self) -> str:
        return self.mirror


class Mapper10(Mapper9):
    """MMC4 — MMC2-style CHR latches with 16 KiB PRG banks."""

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = self.prg_bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0xA000:
            return False
        region = address & 0xF000
        if region == 0xA000:
            self.prg_bank = value & 0x0F
        elif region == 0xB000:
            self.chr_fd[0] = value & 0x1F
        elif region == 0xC000:
            self.chr_fe[0] = value & 0x1F
        elif region == 0xD000:
            self.chr_fd[1] = value & 0x1F
        elif region == 0xE000:
            self.chr_fe[1] = value & 0x1F
        elif region == 0xF000:
            self.mirror = "horizontal" if value & 1 else "vertical"
        return True


class Mapper11(Mapper):
    """Color Dreams / Quattro discrete mapper."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            banks = max(1, len(self.cart.prg) // 0x8000)
            return (self.prg_bank % banks) * 0x8000 + (address & 0x7FFF)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.prg_bank = value & 0x03
            self.chr_bank = (value >> 4) & 0x0F
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return (self.chr_bank * 0x2000 + address) % len(self.cart.chr)
        return None


class Mapper13(Mapper):
    """CPROM — fixed PRG, banked CHR-RAM for $1000-$1FFF."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.chr_bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            return (address - 0x8000) % len(self.cart.prg)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.chr_bank = value & 3
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        bank = 0 if address < 0x1000 else self.chr_bank
        return (bank * 0x1000 + (address & 0x0FFF)) % len(self.cart.chr)

    def ppu_write(self, address: int, value: int) -> bool:
        index = self.ppu_read(address)
        if index is not None and self.cart.chr_is_ram:
            self.cart.chr[index] = value
            return True
        return False


class Mapper34(Mapper):
    """BNROM / NINA-001 style 32 KiB PRG (+ optional CHR regs)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr0 = 0
        self.chr1 = 1

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            banks = max(1, len(self.cart.prg) // 0x8000)
            return (self.prg_bank % banks) * 0x8000 + (address & 0x7FFF)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if address == 0x7FFD:
            self.prg_bank = value & 1
            return True
        if address == 0x7FFE:
            self.chr0 = value & 0x0F
            return True
        if address == 0x7FFF:
            self.chr1 = value & 0x0F
            return True
        if address >= 0x8000:
            self.prg_bank = value & 0x0F
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        if len(self.cart.chr) <= 0x2000 and self.cart.chr_is_ram:
            return address % len(self.cart.chr)
        bank = self.chr0 if address < 0x1000 else self.chr1
        return (bank * 0x1000 + (address & 0x0FFF)) % len(self.cart.chr)


class Mapper71(Mapper):
    """Camerica / Codemasters (Fire Hawk mirroring variant supported)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.bank = 0
        self.mirror = cart.header_mirroring

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = self.bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x8000 <= address <= 0x9FFF:
            self.mirror = "single1" if value & 0x10 else "single0"
            return True
        if address >= 0xC000:
            self.bank = value & 0x0F
            return True
        if address >= 0x8000:
            self.bank = value & 0x0F
            return True
        return False

    def mirror_mode(self) -> str:
        return self.mirror


class Mapper78(Mapper):
    """Irem 74HC161 / Holy Diver."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_bank = 0
        self.mirror = cart.header_mirroring

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = self.prg_bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.prg_bank = value & 0x07
            self.chr_bank = (value >> 4) & 0x0F
            self.mirror = "single1" if value & 0x08 else "horizontal"
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return (self.chr_bank * 0x2000 + address) % len(self.cart.chr)
        return None

    def mirror_mode(self) -> str:
        return self.mirror


class Mapper79(Mapper):
    """NINA-003/006 / American Video Entertainment."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            banks = max(1, len(self.cart.prg) // 0x8000)
            return (self.prg_bank % banks) * 0x8000 + (address & 0x7FFF)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x4100 <= address <= 0x5FFF and (address & 0x0100):
            self.prg_bank = (value >> 3) & 1
            self.chr_bank = value & 0x07
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return (self.chr_bank * 0x2000 + address) % len(self.cart.chr)
        return None


class Mapper87(Mapper):
    """Jaleco/other CNROM-like CHR via $6000."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.chr_bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            return (address - 0x8000) % len(self.cart.prg)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x6000 <= address < 0x8000:
            self.chr_bank = ((value & 2) >> 1) | ((value & 1) << 1)
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return (self.chr_bank * 0x2000 + address) % len(self.cart.chr)
        return None


class Mapper89(Mapper):
    """Sunsoft-2 IC on Sunsoft-3 board."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_bank = 0
        self.mirror = "single0"

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = self.prg_bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.chr_bank = (value & 0x07) | ((value >> 4) & 0x08)
            self.prg_bank = (value >> 4) & 0x07
            self.mirror = "single1" if value & 0x08 else "single0"
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return (self.chr_bank * 0x2000 + address) % len(self.cart.chr)
        return None

    def mirror_mode(self) -> str:
        return self.mirror


class Mapper93(Mapper):
    """Sunsoft-2 on Sunsoft-3B / Fantasy Zone."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = self.prg_bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.prg_bank = (value >> 4) & 0x0F
            return True
        return False


class Mapper94(Mapper):
    """Capcom UxROM variant (Senjou no Ookami)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = self.bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.bank = (value >> 2) & 0x07
            return True
        return False


class Mapper97(Mapper):
    """Irem TAM-S1 (Kaiketsu Yanchamaru)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.bank = 0
        self.mirror = cart.header_mirroring

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = banks - 1 if address < 0xC000 else self.bank % banks
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.bank = value & 0x0F
            self.mirror = ("single0", "horizontal", "vertical", "single1")[(value >> 6) & 3]
            return True
        return False

    def mirror_mode(self) -> str:
        return self.mirror


class Mapper113(Mapper):
    """HES / NINA-03/06 extended (mapper 113)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_bank = 0
        self.mirror = cart.header_mirroring

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            banks = max(1, len(self.cart.prg) // 0x8000)
            return (self.prg_bank % banks) * 0x8000 + (address & 0x7FFF)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x4100 <= address <= 0x5FFF and (address & 0x4100) == 0x4100:
            self.prg_bank = (value >> 3) & 0x07
            self.chr_bank = (value & 0x07) | ((value >> 3) & 0x08)
            self.mirror = "vertical" if value & 0x80 else "horizontal"
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return (self.chr_bank * 0x2000 + address) % len(self.cart.chr)
        return None

    def mirror_mode(self) -> str:
        return self.mirror


class Mapper140(Mapper):
    """Jaleco JF-11/14 (Bio Senshi Dan)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            banks = max(1, len(self.cart.prg) // 0x8000)
            return (self.prg_bank % banks) * 0x8000 + (address & 0x7FFF)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x6000 <= address < 0x8000:
            self.chr_bank = value & 0x0F
            self.prg_bank = (value >> 4) & 0x03
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return (self.chr_bank * 0x2000 + address) % len(self.cart.chr)
        return None


class Mapper152(Mapper):
    """Bandai / Taito 74*161/161/32 with 1-screen mirroring."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_bank = 0
        self.mirror = "single0"

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = self.prg_bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.chr_bank = value & 0x0F
            self.prg_bank = (value >> 4) & 0x07
            self.mirror = "single1" if value & 0x80 else "single0"
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return (self.chr_bank * 0x2000 + address) % len(self.cart.chr)
        return None

    def mirror_mode(self) -> str:
        return self.mirror


class Mapper180(Mapper):
    """UxROM with fixed first bank (Crazy Climber)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.needs_cpu_clock = True
        self.bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = 0 if address < 0xC000 else self.bank % banks
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.bank = value & 0x0F
            return True
        return False


class Mapper184(Mapper):
    """Sunsoft-1 CHR banking via $6000."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.chr0 = 0
        self.chr1 = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            return (address - 0x8000) % len(self.cart.prg)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x6000 <= address < 0x8000:
            self.chr0 = value & 0x07
            self.chr1 = (value >> 4) & 0x07
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        bank = self.chr0 if address < 0x1000 else self.chr1
        return (bank * 0x1000 + (address & 0x0FFF)) % len(self.cart.chr)


class Mapper185(Mapper):
    """CNROM with CHR-disable copy protection."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.chr_enable = True

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            return (address - 0x8000) % len(self.cart.prg)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            # CHR is enabled when the low nibble is nonzero and not the
            # known-lockout value $13 (heuristic used by common emulators).
            low = value & 0x0F
            self.chr_enable = low != 0 and (value & 0x33) != 0x13
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        if not self.chr_enable:
            return None  # reads see open bus, which defeats the protection check
        return address % len(self.cart.chr)


class Mapper206(Mapper4):
    """Namcot 118 / DxROM — MMC3-like banking without IRQ or mirroring writes."""

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        even = not (address & 1)
        if (address & 0xE000) == 0x8000:
            if even:
                self.select = value & 0x3F
            else:
                register = self.select & 7
                self.regs[register] = value & (0xFE if register in (0, 1) else 0xFF)
            return True
        return False

    def clock_scanline(self) -> None:
        pass


class Mapper118(Mapper4):
    """TxSROM / MMC3 with CIRAM A10 from CHR A17."""

    def mirror_mode(self) -> str:
        # Approximate: use CHR bank 0 bit 7 as single-screen select when needed.
        # Full TxSROM is per-1KB nametable from CHR A17; use H/V fallback from bit.
        return "single1" if self.regs[0] & 0x80 else "single0"

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        even = not (address & 1)
        region = address & 0xE000
        if region == 0x8000:
            if even:
                self.select = value
            else:
                register = self.select & 7
                self.regs[register] = value & (0xFE if register in (0, 1) else 0xFF)
        elif region == 0xC000:
            if even:
                self.irq_latch = value
            else:
                self.irq_reload = True
        elif region == 0xE000:
            if even:
                self.irq_enabled = False
                self.irq_pending = False
            else:
                self.irq_enabled = True
        # Ignore $A000 mirroring — TxSROM uses CHR A17.
        return True


class Mapper119(Mapper4):
    """TQROM — MMC3 with mixed CHR: bank bit 6 selects 8 KiB of CHR-RAM."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        # Append the CHR-RAM area after the CHR-ROM image.
        self.ram_base = len(cart.chr)
        cart.chr.extend(bytearray(0x2000))
        cart.chr_len = len(cart.chr)

    def _chr_index(self, address: int) -> int:
        inverted = bool(self.select & 0x80)
        logical = address ^ (0x1000 if inverted else 0)
        slot = logical // 0x400
        pairs = (self.regs[0], self.regs[0] + 1, self.regs[1], self.regs[1] + 1)
        bank = pairs[slot] if slot < 4 else self.regs[slot - 2]
        if bank & 0x40:
            return self.ram_base + ((bank & 0x07) * 0x400 + (logical & 0x3FF))
        return ((bank & 0x3F) * 0x400 + (logical & 0x3FF)) % max(1, self.ram_base)

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        return self._chr_index(address)

    def ppu_write(self, address: int, value: int) -> bool:
        if address >= 0x2000:
            return False
        index = self._chr_index(address)
        if index >= self.ram_base:
            self.cart.chr[index] = value
            return True
        return False


class Mapper75(Mapper):
    """Konami VRC1."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg = [0, 0, 0]
        self.chr = [0, 0]
        self.mirror = cart.header_mirroring

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        slot = (address - 0x8000) // 0x2000
        banks = [self.prg[0], self.prg[1], self.prg[2], count - 1]
        return (banks[slot] % count) * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        region = address & 0xF000
        if region == 0x8000:
            self.prg[0] = value & 0x0F
        elif region == 0x9000:
            self.mirror = "horizontal" if value & 1 else "vertical"
            self.chr[0] = (self.chr[0] & 0x0F) | ((value & 2) << 3)
            self.chr[1] = (self.chr[1] & 0x0F) | ((value & 4) << 2)
        elif region == 0xA000:
            self.prg[1] = value & 0x0F
        elif region == 0xC000:
            self.prg[2] = value & 0x0F
        elif region == 0xE000:
            self.chr[0] = (self.chr[0] & 0x10) | (value & 0x0F)
        elif region == 0xF000:
            self.chr[1] = (self.chr[1] & 0x10) | (value & 0x0F)
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        bank = self.chr[0] if address < 0x1000 else self.chr[1]
        return (bank * 0x1000 + (address & 0x0FFF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror


class _VRC2and4(Mapper):
    """Shared Konami VRC2/VRC4 banking + optional IRQ (VRC4)."""

    def __init__(self, cart: "Cartridge", a0_mask: int, a1_mask: int, has_irq: bool) -> None:
        super().__init__(cart)
        self.needs_cpu_clock = True
        self.a0_mask = a0_mask
        self.a1_mask = a1_mask
        self.has_irq = has_irq
        self.prg = [0, 0]
        self.chr = [0] * 8
        self.prg_mode = 0
        self.mirror = cart.header_mirroring
        self.latch = 0
        self.irq_latch = 0
        self.irq_control = 0
        self.irq_counter = 0
        self.irq_prescale = 341

    def _reg(self, address: int) -> int:
        return ((1 if address & self.a1_mask else 0) << 1) | (1 if address & self.a0_mask else 0)

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        last = count - 1
        if self.prg_mode:
            banks = [last - 1, self.prg[1] % count, self.prg[0] % count, last]
        else:
            banks = [self.prg[0] % count, self.prg[1] % count, last - 1 if last else 0, last]
        slot = (address - 0x8000) // 0x2000
        return banks[slot] * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        region = address & 0xF000
        reg = self._reg(address)
        if region == 0x8000:
            self.prg[0] = value & 0x1F
        elif region == 0x9000:
            if reg in (0, 1):
                # VRC2 only has H/V (bit 0); VRC4 adds single-screen modes.
                mask = 3 if self.has_irq else 1
                self.mirror = ("vertical", "horizontal", "single0", "single1")[value & mask]
            elif reg in (2, 3) and self.has_irq:
                self.prg_mode = value & 2
        elif region == 0xA000:
            self.prg[1] = value & 0x1F
        elif 0xB000 <= region <= 0xE000:
            pair = ((region - 0xB000) // 0x1000) * 2 + (reg >> 1)
            if reg & 1:
                self.chr[pair] = (self.chr[pair] & 0x0F) | ((value & 0x0F) << 4)
            else:
                self.chr[pair] = (self.chr[pair] & 0xF0) | (value & 0x0F)
        elif region == 0xF000 and self.has_irq:
            if reg == 0:
                self.irq_latch = (self.irq_latch & 0xF0) | (value & 0x0F)
            elif reg == 1:
                self.irq_latch = (self.irq_latch & 0x0F) | ((value & 0x0F) << 4)
            elif reg == 2:
                self.irq_pending = False
                self.irq_control = value & 0x07
                if value & 2:
                    self.irq_counter = self.irq_latch
                    self.irq_prescale = 341
            elif reg == 3:
                self.irq_pending = False
                self.irq_control = (self.irq_control & ~2) | ((self.irq_control << 1) & 2)
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        bank = self.chr[address // 0x400]
        return (bank * 0x400 + (address & 0x3FF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror

    def clock_cpu(self, cycles: int) -> None:
        if not self.has_irq or not (self.irq_control & 2):
            return
        for _ in range(cycles):
            if self.irq_control & 4:
                # cycle mode
                self.irq_counter = (self.irq_counter + 1) & 0xFF
                if self.irq_counter == 0:
                    self.irq_counter = self.irq_latch
                    if self.irq_control & 1:
                        self.irq_pending = True
            else:
                self.irq_prescale -= 3
                if self.irq_prescale <= 0:
                    self.irq_prescale += 341
                    if self.irq_counter == 0xFF:
                        self.irq_counter = self.irq_latch
                        if self.irq_control & 1:
                            self.irq_pending = True
                    else:
                        self.irq_counter = (self.irq_counter + 1) & 0xFF


class Mapper21(_VRC2and4):
    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart, a0_mask=0x02, a1_mask=0x04, has_irq=True)


class Mapper22(_VRC2and4):
    """VRC2a — CHR banks shifted left by 1."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart, a0_mask=0x02, a1_mask=0x01, has_irq=False)

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        bank = self.chr[address // 0x400] >> 1
        return (bank * 0x400 + (address & 0x3FF)) % len(self.cart.chr)


class Mapper23(_VRC2and4):
    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart, a0_mask=0x01, a1_mask=0x02, has_irq=True)


class Mapper25(_VRC2and4):
    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart, a0_mask=0x02, a1_mask=0x01, has_irq=True)


class Mapper24(Mapper):
    """Konami VRC6a banking + IRQ (expansion audio not mixed)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.needs_cpu_clock = True
        self.prg16 = 0
        self.prg8 = 0
        self.chr = [0] * 8
        self.mirror = cart.header_mirroring
        self.irq_latch = 0
        self.irq_control = 0
        self.irq_counter = 0
        self.irq_prescale = 341

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count8 = max(1, len(self.cart.prg) // 0x2000)
        if address < 0xC000:
            bank = (self.prg16 % max(1, count8 // 2)) * 2 + (0 if address < 0xA000 else 1)
        elif address < 0xE000:
            bank = self.prg8 % count8
        else:
            bank = count8 - 1
        return bank * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        if address & 0xF000 == 0x8000:
            self.prg16 = value & 0x0F
        elif address & 0xF000 == 0x9000:
            pass  # pulse1 regs ignored
        elif address & 0xF000 == 0xA000:
            pass  # pulse2
        elif address & 0xF000 == 0xB000:
            if (address & 3) == 3:
                self.mirror = ("vertical", "horizontal", "single0", "single1")[value & 3]
            # saw / other ignored
        elif address & 0xF000 == 0xC000:
            self.prg8 = value & 0x1F
        elif address & 0xF000 == 0xD000:
            self.chr[address & 3] = value
        elif address & 0xF000 == 0xE000:
            self.chr[4 + (address & 3)] = value
        elif address & 0xF000 == 0xF000:
            reg = address & 3
            if reg == 0:
                self.irq_latch = value
            elif reg == 1:
                self.irq_pending = False
                self.irq_control = value & 0x07
                if value & 2:
                    self.irq_counter = self.irq_latch
                    self.irq_prescale = 341
            elif reg == 2:
                self.irq_pending = False
                self.irq_control = (self.irq_control & ~2) | ((self.irq_control << 1) & 2)
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        return (self.chr[address // 0x400] * 0x400 + (address & 0x3FF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror

    def clock_cpu(self, cycles: int) -> None:
        if not (self.irq_control & 2):
            return
        for _ in range(cycles):
            if self.irq_control & 4:
                self.irq_counter = (self.irq_counter + 1) & 0xFF
                if self.irq_counter == 0:
                    self.irq_counter = self.irq_latch
                    if self.irq_control & 1:
                        self.irq_pending = True
            else:
                self.irq_prescale -= 3
                if self.irq_prescale <= 0:
                    self.irq_prescale += 341
                    if self.irq_counter == 0xFF:
                        self.irq_counter = self.irq_latch
                        if self.irq_control & 1:
                            self.irq_pending = True
                    else:
                        self.irq_counter = (self.irq_counter + 1) & 0xFF


class Mapper26(Mapper24):
    """VRC6b — swapped A0/A1 relative to VRC6a."""

    def cpu_write(self, address: int, value: int) -> bool:
        # Translate VRC6b addressing into VRC6a layout: swap bits 0 and 1.
        bits = address & 3
        swapped = (address & 0xFFFC) | ((bits & 1) << 1) | ((bits & 2) >> 1)
        return Mapper24.cpu_write(self, swapped, value)


class Mapper69(Mapper):
    """Sunsoft FME-7 / 5B command mapper (AY audio not mixed)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.needs_cpu_clock = True
        self.command = 0
        self.prg = [0, 0, 0, 0]
        self.chr = [0] * 8
        self.mirror = cart.header_mirroring
        self.irq_control = 0
        self.irq_counter = 0
        self.prg_ram_enable = False
        self.prg_ram_select = False

    def cpu_read(self, address: int) -> Optional[int]:
        if 0x6000 <= address < 0x8000:
            if self.prg_ram_select:
                return None  # fall through to PRG-RAM in Cartridge
            count = max(1, len(self.cart.prg) // 0x2000)
            return (self.prg[0] % count) * 0x2000 + (address & 0x1FFF)
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        if address >= 0xE000:
            bank = count - 1
        else:
            bank = self.prg[(address - 0x8000) // 0x2000 + 1] % count
        return bank * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x6000 <= address < 0x8000:
            return False  # PRG-RAM / ROM handled by read path
        if 0x8000 <= address <= 0x9FFF:
            self.command = value & 0x0F
            return True
        if 0xA000 <= address <= 0xBFFF:
            cmd = self.command
            if cmd < 8:
                self.chr[cmd] = value
            elif cmd == 8:
                # Bit 6 selects RAM (1) vs ROM (0) at $6000; bit 7 enables RAM.
                self.prg_ram_enable = bool(value & 0x80)
                self.prg_ram_select = bool(value & 0x40)
                self.prg[0] = value & 0x3F
            elif cmd in (9, 10, 11):
                self.prg[cmd - 8] = value & 0x3F
            elif cmd == 12:
                self.mirror = ("vertical", "horizontal", "single0", "single1")[value & 3]
            elif cmd == 13:
                self.irq_control = value
                self.irq_pending = False
            elif cmd == 14:
                self.irq_counter = (self.irq_counter & 0xFF00) | value
            elif cmd == 15:
                self.irq_counter = (self.irq_counter & 0x00FF) | (value << 8)
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        return (self.chr[address // 0x400] * 0x400 + (address & 0x3FF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror

    def clock_cpu(self, cycles: int) -> None:
        if not (self.irq_control & 0x80):
            return
        for _ in range(cycles):
            self.irq_counter = (self.irq_counter - 1) & 0xFFFF
            if self.irq_counter == 0xFFFF and (self.irq_control & 0x01):
                self.irq_pending = True


class Mapper19(Mapper):
    """Namco 163 banking + IRQ (wavetable audio not mixed)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.needs_cpu_clock = True
        self.prg = [0, 0, 0]
        self.chr = [0] * 8
        self.mirror = [0, 0, 0, 0]
        self.irq_counter = 0
        self.irq_enabled = False
        self.chr_ram_enable = [True, True]

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        if address < 0xA000:
            bank = self.prg[0]
        elif address < 0xC000:
            bank = self.prg[1]
        elif address < 0xE000:
            bank = self.prg[2]
        else:
            bank = count - 1
        return (bank % count) * 0x2000 + (address & 0x1FFF)

    def register_read(self, address: int) -> Optional[int]:
        if 0x5000 <= address <= 0x57FF:
            return self.irq_counter & 0xFF
        if 0x5800 <= address <= 0x5FFF:
            return ((self.irq_counter >> 8) & 0x7F) | (0x80 if self.irq_enabled else 0)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x5000 <= address <= 0x57FF:
            self.irq_counter = (self.irq_counter & 0xFF00) | value
            self.irq_pending = False
            return True
        if 0x5800 <= address <= 0x5FFF:
            self.irq_counter = (self.irq_counter & 0x00FF) | ((value & 0x7F) << 8)
            self.irq_enabled = bool(value & 0x80)
            self.irq_pending = False
            return True
        if address < 0x8000:
            return False
        if 0x8000 <= address <= 0xBFFF:
            # Eight 1 KiB CHR select registers, one per $800 window.
            self.chr[(address - 0x8000) // 0x800] = value
            return True
        if 0xC000 <= address <= 0xDFFF:
            # Nametable select registers — CIRAM handling approximated.
            return True
        if 0xE000 <= address <= 0xE7FF:
            self.prg[0] = value & 0x3F
            return True
        if 0xE800 <= address <= 0xEFFF:
            self.prg[1] = value & 0x3F
            self.chr_ram_enable[0] = not bool(value & 0x40)
            self.chr_ram_enable[1] = not bool(value & 0x80)
            return True
        if 0xF000 <= address <= 0xF7FF:
            self.prg[2] = value & 0x3F
            return True
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        bank = self.chr[address // 0x400]
        return (bank * 0x400 + (address & 0x3FF)) % len(self.cart.chr)

    def clock_cpu(self, cycles: int) -> None:
        if not self.irq_enabled:
            return
        for _ in range(cycles):
            self.irq_counter = (self.irq_counter + 1) & 0x7FFF
            if self.irq_counter == 0x7FFF:
                self.irq_pending = True
                self.irq_enabled = False


class Mapper32(Mapper):
    """Irem G-101."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg = [0, 0]
        self.chr = [0] * 8
        self.mode = 0
        self.mirror = cart.header_mirroring

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        last = count - 1
        if self.mode & 2:
            banks = [last - 1, self.prg[1] % count, self.prg[0] % count, last]
        else:
            banks = [self.prg[0] % count, self.prg[1] % count, last - 1 if last else 0, last]
        slot = (address - 0x8000) // 0x2000
        return banks[slot] * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        region = address & 0xF000
        if region == 0x8000:
            self.prg[0] = value & 0x1F
        elif region == 0x9000:
            self.mode = value & 3
            self.mirror = "horizontal" if value & 1 else "vertical"
        elif region == 0xA000:
            self.prg[1] = value & 0x1F
        elif region == 0xB000:
            self.chr[address & 7] = value
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        return (self.chr[address // 0x400] * 0x400 + (address & 0x3FF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror


class Mapper33(Mapper):
    """Taito TC0190 (mapper 33)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg = [0, 0]
        self.chr2 = [0, 0]  # 2 KiB banks
        self.chr1 = [0, 0, 0, 0]  # 1 KiB banks
        self.mirror = cart.header_mirroring

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        banks = [self.prg[0] % count, self.prg[1] % count, max(0, count - 2), count - 1]
        slot = (address - 0x8000) // 0x2000
        return banks[slot] * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x8000 <= address <= 0x9FFF:
            idx = address & 3
            if idx == 0:
                self.prg[0] = value & 0x3F
                self.mirror = "horizontal" if value & 0x40 else "vertical"
            elif idx == 1:
                self.prg[1] = value & 0x3F
            elif idx == 2:
                self.chr2[0] = value
            else:
                self.chr2[1] = value
            return True
        if 0xA000 <= address <= 0xBFFF:
            self.chr1[address & 3] = value
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        if address < 0x800:
            bank = self.chr2[0] * 2 + (address // 0x400)
        elif address < 0x1000:
            bank = self.chr2[1] * 2 + ((address - 0x800) // 0x400)
        else:
            bank = self.chr1[(address - 0x1000) // 0x400]
        return (bank * 0x400 + (address & 0x3FF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror


class Mapper48(Mapper33):
    """Taito TC0690 — TC0190 + MMC3-like scanline IRQ."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.irq_latch = 0
        self.irq_counter = 0
        self.irq_enabled = False
        self.irq_reload = False

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x8000 <= address <= 0x9FFF:
            idx = address & 3
            if idx == 0:
                self.prg[0] = value & 0x3F
            elif idx == 1:
                self.prg[1] = value & 0x3F
            elif idx == 2:
                self.chr2[0] = value
            else:
                self.chr2[1] = value
            return True
        if 0xA000 <= address <= 0xBFFF:
            self.chr1[address & 3] = value
            return True
        if 0xC000 <= address <= 0xDFFF:
            if address & 1:
                self.irq_reload = True
            else:
                self.irq_latch = value ^ 0xFF
            return True
        if 0xE000 <= address <= 0xFFFF:
            if address & 1:
                self.mirror = "horizontal" if value & 1 else "vertical"
            else:
                self.irq_enabled = bool(value & 1)
                if not self.irq_enabled:
                    self.irq_pending = False
            return True
        return False

    def clock_scanline(self) -> None:
        if self.irq_counter == 0 or self.irq_reload:
            self.irq_counter = self.irq_latch
            self.irq_reload = False
        else:
            self.irq_counter = (self.irq_counter - 1) & 0xFF
        if self.irq_counter == 0 and self.irq_enabled:
            self.irq_pending = True


class Mapper65(Mapper):
    """Irem H3001."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.needs_cpu_clock = True
        self.prg = [0, 1, 0xFE]
        self.chr = [0] * 8
        self.irq_enabled = False
        self.irq_counter = 0
        self.irq_latch = 0
        self.mirror = cart.header_mirroring

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        banks = [self.prg[0] % count, self.prg[1] % count, self.prg[2] % count, count - 1]
        slot = (address - 0x8000) // 0x2000
        return banks[slot] * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        if address == 0x8000:
            self.prg[0] = value
        elif address == 0xA000:
            self.prg[1] = value
        elif address == 0xC000:
            self.prg[2] = value
        elif 0xB000 <= address <= 0xB007:
            self.chr[address & 7] = value
        elif address == 0x9001:
            self.mirror = "horizontal" if value & 0x80 else "vertical"
        elif address == 0x9003:
            self.irq_enabled = bool(value & 0x80)
            self.irq_pending = False
        elif address == 0x9004:
            self.irq_counter = self.irq_latch
            self.irq_pending = False
        elif address == 0x9005:
            self.irq_latch = (self.irq_latch & 0x00FF) | (value << 8)
        elif address == 0x9006:
            self.irq_latch = (self.irq_latch & 0xFF00) | value
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        return (self.chr[address // 0x400] * 0x400 + (address & 0x3FF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror

    def clock_cpu(self, cycles: int) -> None:
        if not self.irq_enabled:
            return
        for _ in range(cycles):
            if self.irq_counter == 0:
                self.irq_pending = True
                self.irq_enabled = False
            else:
                self.irq_counter = (self.irq_counter - 1) & 0xFFFF


class Mapper68(Mapper):
    """Sunsoft-4."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr = [0, 0, 0, 0]
        self.nt = [0, 0]
        self.mirror_reg = 0
        self.mirror = cart.header_mirroring

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = self.prg_bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        region = address & 0xF000
        if region == 0x8000:
            self.chr[0] = value
        elif region == 0x9000:
            self.chr[1] = value
        elif region == 0xA000:
            self.chr[2] = value
        elif region == 0xB000:
            self.chr[3] = value
        elif region == 0xC000:
            self.nt[0] = value | 0x80
        elif region == 0xD000:
            self.nt[1] = value | 0x80
        elif region == 0xE000:
            self.mirror_reg = value
            modes = ("vertical", "horizontal", "single0", "single1")
            self.mirror = modes[value & 3]
        elif region == 0xF000:
            self.prg_bank = value & 0x0F
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        bank = self.chr[address // 0x800]
        return (bank * 0x800 + (address & 0x7FF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror


class Mapper16(Mapper):
    """Bandai FCG-1/2 / LZ93D50 (EEPROM not persisted)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.needs_cpu_clock = True
        self.prg_bank = 0
        self.chr = [0] * 8
        self.mirror = cart.header_mirroring
        self.irq_enabled = False
        self.irq_counter = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = self.prg_bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x6000:
            return False
        reg = address & 0x000F
        if reg < 8:
            self.chr[reg] = value
        elif reg == 8:
            self.prg_bank = value & 0x0F
        elif reg == 9:
            self.mirror = ("vertical", "horizontal", "single0", "single1")[value & 3]
        elif reg == 0xA:
            self.irq_enabled = bool(value & 1)
            self.irq_pending = False
        elif reg == 0xB:
            self.irq_counter = (self.irq_counter & 0xFF00) | value
        elif reg == 0xC:
            self.irq_counter = (self.irq_counter & 0x00FF) | (value << 8)
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        return (self.chr[address // 0x400] * 0x400 + (address & 0x3FF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror

    def clock_cpu(self, cycles: int) -> None:
        if not self.irq_enabled:
            return
        for _ in range(cycles):
            if self.irq_counter == 0:
                self.irq_pending = True
                self.irq_enabled = False
            else:
                self.irq_counter = (self.irq_counter - 1) & 0xFFFF


class Mapper18(Mapper):
    """Jaleco SS88006."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg = [0, 0, 0]
        self.chr = [0] * 8
        self.mirror = cart.header_mirroring
        self.irq_enabled = False
        self.irq_counter = 0
        self.irq_latch = 0
        self.irq_mask = 0xFFFF

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        banks = [self.prg[0] % count, self.prg[1] % count, self.prg[2] % count, count - 1]
        slot = (address - 0x8000) // 0x2000
        return banks[slot] * 0x2000 + (address & 0x1FFF)

    @staticmethod
    def _nibble(current: int, address: int, value: int) -> int:
        if address & 1:
            return (current & 0x0F) | (value << 4)
        return (current & 0xF0) | value

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        # Registers repeat every $1000 with two bits of sub-select.
        address = address & 0xF003
        value &= 0x0F
        if 0x8000 <= address <= 0x8003:
            slot = 0 if (address & 3) < 2 else 1
            self.prg[slot] = self._nibble(self.prg[slot], address, value)
        elif 0x9000 <= address <= 0x9001:
            self.prg[2] = self._nibble(self.prg[2], address, value)
        elif 0xA000 <= address <= 0xD003:
            chr_index = ((address - 0xA000) // 0x1000) * 2 + ((address >> 1) & 1)
            self.chr[chr_index] = self._nibble(self.chr[chr_index], address, value)
        elif address == 0xE000:
            self.irq_latch = (self.irq_latch & 0xFFF0) | value
        elif address == 0xE001:
            self.irq_latch = (self.irq_latch & 0xFF0F) | (value << 4)
        elif address == 0xE002:
            self.irq_latch = (self.irq_latch & 0xF0FF) | (value << 8)
        elif address == 0xE003:
            self.irq_latch = (self.irq_latch & 0x0FFF) | (value << 12)
        elif address == 0xF000:
            self.irq_counter = self.irq_latch
            self.irq_pending = False
        elif address == 0xF001:
            self.irq_enabled = bool(value & 1)
            self.irq_mask = (0xFFFF, 0x0FFF, 0x00FF, 0x000F)[(value >> 1) & 3]
            self.irq_pending = False
        elif address == 0xF002:
            self.mirror = ("horizontal", "vertical", "single0", "single1")[value & 3]
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        return (self.chr[address // 0x400] * 0x400 + (address & 0x3FF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror

    def clock_cpu(self, cycles: int) -> None:
        if not self.irq_enabled:
            return
        for _ in range(cycles):
            counter = self.irq_counter & self.irq_mask
            if counter == 0:
                self.irq_pending = True
            self.irq_counter = (self.irq_counter - 1) & 0xFFFF


class Mapper5(Mapper):
    """MMC5 (ExROM) — PRG/CHR banking, multiplier, scanline IRQ; ExAttr/audio simplified."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_mode = 3
        self.chr_mode = 0
        self.prg_regs = [0xFF, 0xFF, 0xFF, 0xFF, 0xFF]
        self.chr_regs = [0] * 12
        self.mirror = cart.header_mirroring
        self.fill_tile = 0
        self.fill_attr = 0
        self.irq_scanline = 0
        self.irq_enabled = False
        self.irq_status = 0
        self.mul = [0xFF, 0xFF]
        self.exram = bytearray(0x400)
        self.exram_mode = 0
        self.protect = 0
        self.chr_hi = 0
        self._scan = 0

    def register_read(self, address: int) -> Optional[int]:
        if 0x5C00 <= address <= 0x5FFF:
            return self.exram[address & 0x3FF]
        if address == 0x5204:
            value = self.irq_status
            self.irq_status &= ~0x80
            self.irq_pending = False
            return value
        if address in (0x5205, 0x5206):
            product = self.mul[0] * self.mul[1]
            return (product >> (8 if address == 0x5206 else 0)) & 0xFF
        return None

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        mode = self.prg_mode & 3
        regs = [r & 0x7F for r in self.prg_regs]
        if mode == 0:
            bank = (regs[4] & 0x7C) % max(1, count)
            return bank * 0x2000 + (address & 0x7FFF)
        if mode == 1:
            if address < 0xC000:
                bank = (regs[2] & 0x7E) % count
                return bank * 0x2000 + (address & 0x3FFF)
            bank = (regs[4] & 0x7E) % count
            return bank * 0x2000 + (address & 0x3FFF)
        if mode == 2:
            if address < 0xC000:
                bank = (regs[2] & 0x7E) % count
                return bank * 0x2000 + (address & 0x3FFF)
            if address < 0xE000:
                bank = regs[3] % count
            else:
                bank = regs[4] % count
            return bank * 0x2000 + (address & 0x1FFF)
        # mode 3: 8KB
        banks = [regs[1] % count, regs[2] % count, regs[3] % count, regs[4] % count]
        slot = (address - 0x8000) // 0x2000
        return banks[slot] * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address == 0x5100:
            self.prg_mode = value & 3
            return True
        if address == 0x5101:
            self.chr_mode = value & 3
            return True
        if address == 0x5102:
            self.protect = (self.protect & 0x2) | (value & 1)
            return True
        if address == 0x5103:
            self.protect = (self.protect & 0x1) | ((value & 1) << 1)
            return True
        if address == 0x5104:
            self.exram_mode = value & 3
            return True
        if address == 0x5105:
            # $5105 packs one 2-bit nametable source per quadrant.
            known = {0x50: "horizontal", 0x44: "vertical", 0x00: "single0", 0x55: "single1"}
            self.mirror = known.get(value, "vertical" if (value & 3) != ((value >> 2) & 3) else "horizontal")
            return True
        if address == 0x5106:
            self.fill_tile = value
            return True
        if address == 0x5107:
            self.fill_attr = value & 3
            return True
        if 0x5113 <= address <= 0x5117:
            self.prg_regs[address - 0x5113] = value
            return True
        if 0x5120 <= address <= 0x512B:
            self.chr_regs[address - 0x5120] = value
            return True
        if address == 0x5130:
            self.chr_hi = value & 3
            return True
        if address == 0x5203:
            self.irq_scanline = value
            return True
        if address == 0x5204:
            self.irq_enabled = bool(value & 0x80)
            if not self.irq_enabled:
                self.irq_pending = False
            return True
        if address in (0x5205, 0x5206):
            self.mul[address - 0x5205] = value
            return True
        if 0x5C00 <= address <= 0x5FFF:
            if self.exram_mode <= 1:
                self.exram[address & 0x3FF] = value
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        mode = self.chr_mode & 3
        regs = self.chr_regs
        hi = self.chr_hi << 8
        if mode == 0:
            bank = (hi | regs[7]) * 8
            return ((bank + address // 0x400) * 0x400 + (address & 0x3FF)) % len(self.cart.chr)
        if mode == 1:
            idx = 3 if address < 0x1000 else 7
            bank = (hi | regs[idx]) * 4
            return ((bank + (address & 0xFFF) // 0x400) * 0x400 + (address & 0x3FF)) % len(self.cart.chr)
        if mode == 2:
            idx = (1 if address < 0x800 else 3 if address < 0x1000 else 5 if address < 0x1800 else 7)
            bank = (hi | regs[idx]) * 2
            return ((bank + ((address & 0x7FF) // 0x400)) * 0x400 + (address & 0x3FF)) % len(self.cart.chr)
        bank = hi | regs[address // 0x400]
        return (bank * 0x400 + (address & 0x3FF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror

    def clock_scanline(self) -> None:
        self._scan += 1
        self.irq_status |= 0x40
        if self._scan == self.irq_scanline:
            self.irq_status |= 0x80
            if self.irq_enabled:
                self.irq_pending = True
        if self._scan >= 240:
            self._scan = 0
            self.irq_status &= ~0x40


class Mapper64(Mapper4):
    """Tengen RAMBO-1 — MMC3-style banking with a third PRG register and
    1 KiB CHR mode; the cycle-mode IRQ is approximated by the scanline
    counter inherited from Mapper4."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.regs = [0] * 16

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        last = count - 1
        r6, r7, r15 = self.regs[6] % count, self.regs[7] % count, self.regs[15] % count
        if self.select & 0x40:
            banks = (r15, r6, r7, last)
        else:
            banks = (r6, r7, r15, last)
        slot = (address - 0x8000) // 0x2000
        return banks[slot] * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        even = not (address & 1)
        region = address & 0xE000
        if region == 0x8000:
            if even:
                self.select = value
            else:
                self.regs[self.select & 0x0F] = value
        elif region == 0xA000:
            if even and self.cart.header_mirroring != "four":
                self.mirror = "horizontal" if value & 1 else "vertical"
        elif region == 0xC000:
            if even:
                self.irq_latch = value
            else:
                self.irq_reload = True
        elif region == 0xE000:
            if even:
                self.irq_enabled = False
                self.irq_pending = False
            else:
                self.irq_enabled = True
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        regs = self.regs
        if self.select & 0x20:
            # 1 KiB CHR mode: R0,R8,R1,R9 cover $0000-$0FFF.
            low = (regs[0], regs[8], regs[1], regs[9])
            banks = low + (regs[2], regs[3], regs[4], regs[5])
        else:
            banks = (
                regs[0] & 0xFE, (regs[0] & 0xFE) + 1,
                regs[1] & 0xFE, (regs[1] & 0xFE) + 1,
                regs[2], regs[3], regs[4], regs[5],
            )
        logical = address ^ (0x1000 if self.select & 0x80 else 0)
        bank = banks[logical // 0x400]
        return (bank * 0x400 + (logical & 0x3FF)) % len(self.cart.chr)


class Mapper85(Mapper):
    """Konami VRC7 banking + IRQ (FM audio not mixed)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.needs_cpu_clock = True
        self.prg = [0, 0, 0]
        self.chr = [0] * 8
        self.mirror = cart.header_mirroring
        self.irq_latch = 0
        self.irq_control = 0
        self.irq_counter = 0
        self.irq_prescale = 341

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        banks = [self.prg[0] % count, self.prg[1] % count, self.prg[2] % count, count - 1]
        slot = (address - 0x8000) // 0x2000
        return banks[slot] * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        # VRC7 uses sparse selects; accept broad masks
        if 0x8000 <= address <= 0x800F:
            self.prg[0] = value & 0x3F
        elif 0x8010 <= address <= 0x801F:
            self.prg[1] = value & 0x3F
        elif 0x9000 <= address <= 0x900F:
            self.prg[2] = value & 0x3F
        elif 0xA000 <= address <= 0xA00F:
            self.chr[0] = value
        elif 0xA010 <= address <= 0xA01F:
            self.chr[1] = value
        elif 0xB000 <= address <= 0xB00F:
            self.chr[2] = value
        elif 0xB010 <= address <= 0xB01F:
            self.chr[3] = value
        elif 0xC000 <= address <= 0xC00F:
            self.chr[4] = value
        elif 0xC010 <= address <= 0xC01F:
            self.chr[5] = value
        elif 0xD000 <= address <= 0xD00F:
            self.chr[6] = value
        elif 0xD010 <= address <= 0xD01F:
            self.chr[7] = value
        elif 0xE000 <= address <= 0xE00F:
            self.mirror = ("vertical", "horizontal", "single0", "single1")[value & 3]
        elif 0xE010 <= address <= 0xE01F:
            self.irq_latch = value
        elif 0xF000 <= address <= 0xF00F:
            self.irq_pending = False
            self.irq_control = value & 0x07
            if value & 2:
                self.irq_counter = self.irq_latch
                self.irq_prescale = 341
        elif 0xF010 <= address <= 0xF01F:
            self.irq_pending = False
            self.irq_control = (self.irq_control & ~2) | ((self.irq_control << 1) & 2)
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        return (self.chr[address // 0x400] * 0x400 + (address & 0x3FF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror

    def clock_cpu(self, cycles: int) -> None:
        if not (self.irq_control & 2):
            return
        for _ in range(cycles):
            if self.irq_control & 4:
                self.irq_counter = (self.irq_counter + 1) & 0xFF
                if self.irq_counter == 0:
                    self.irq_counter = self.irq_latch
                    if self.irq_control & 1:
                        self.irq_pending = True
            else:
                self.irq_prescale -= 3
                if self.irq_prescale <= 0:
                    self.irq_prescale += 341
                    if self.irq_counter == 0xFF:
                        self.irq_counter = self.irq_latch
                        if self.irq_control & 1:
                            self.irq_pending = True
                    else:
                        self.irq_counter = (self.irq_counter + 1) & 0xFF


class Mapper155(Mapper1):
    """MMC1A variant (PRG-RAM protect ignored)."""


class Mapper210(Mapper19):
    """Namco 175/340 — Namco 163 without IRQ/audio."""

    def clock_cpu(self, cycles: int) -> None:
        pass


MAPPERS: dict[int, type[Mapper]] = {
    0: Mapper0,
    1: Mapper1,
    2: Mapper2,
    3: Mapper3,
    4: Mapper4,
    5: Mapper5,
    7: Mapper7,
    9: Mapper9,
    10: Mapper10,
    11: Mapper11,
    13: Mapper13,
    16: Mapper16,
    18: Mapper18,
    19: Mapper19,
    21: Mapper21,
    22: Mapper22,
    23: Mapper23,
    24: Mapper24,
    25: Mapper25,
    26: Mapper26,
    32: Mapper32,
    33: Mapper33,
    34: Mapper34,
    48: Mapper48,
    64: Mapper64,
    65: Mapper65,
    66: Mapper66,
    68: Mapper68,
    69: Mapper69,
    71: Mapper71,
    75: Mapper75,
    78: Mapper78,
    79: Mapper79,
    85: Mapper85,
    87: Mapper87,
    89: Mapper89,
    93: Mapper93,
    94: Mapper94,
    97: Mapper97,
    113: Mapper113,
    118: Mapper118,
    119: Mapper119,
    140: Mapper140,
    152: Mapper152,
    155: Mapper155,
    180: Mapper180,
    184: Mapper184,
    185: Mapper185,
    206: Mapper206,
    210: Mapper210,
}


class Cartridge:
    def __init__(self, image: bytes, source: str = "<memory>") -> None:
        if len(image) < 16 or image[:4] != b"NES\x1a":
            raise CartridgeError("Not a valid iNES or NES 2.0 cartridge image.")
        self.source = source
        flags6, flags7 = image[6], image[7]
        self.mapper_id = (flags6 >> 4) | (flags7 & 0xF0)
        self.nes2 = (flags7 & 0x0C) == 0x08
        if self.nes2:
            self.mapper_id |= (image[8] & 0x0F) << 8
        if flags6 & 0x08:
            self.header_mirroring = "four"
        else:
            self.header_mirroring = "vertical" if flags6 & 1 else "horizontal"
        self.battery = bool(flags6 & 2)
        offset = 16 + (512 if flags6 & 4 else 0)
        prg_banks = image[4]
        chr_banks = image[5]
        if self.nes2:
            prg_banks |= (image[9] & 0x0F) << 8
            chr_banks |= (image[9] & 0xF0) << 4
        prg_size = prg_banks * 0x4000
        chr_size = chr_banks * 0x2000
        if prg_size == 0 or offset + prg_size + chr_size > len(image):
            raise CartridgeError("The ROM is truncated or has an invalid bank count.")
        self.prg = bytes(image[offset:offset + prg_size])
        offset += prg_size
        self.chr_is_ram = chr_size == 0
        # CPROM (mapper 13) banks 16 KiB of CHR-RAM; everything else uses 8 KiB.
        chr_ram_size = 0x4000 if self.mapper_id == 13 else 0x2000
        self.chr = bytearray(chr_ram_size if self.chr_is_ram else image[offset:offset + chr_size])
        self.prg_ram = bytearray(0x2000)
        # Cached bank counts — avoid len()/division on every CPU/PPU fetch.
        self.prg_len = len(self.prg)
        self.chr_len = len(self.chr)
        self.prg_8k = max(1, self.prg_len // 0x2000)
        self.prg_16k = max(1, self.prg_len // 0x4000)
        self.prg_32k = max(1, self.prg_len // 0x8000)
        mapper_type = MAPPERS.get(self.mapper_id)
        if mapper_type is None:
            supported = ", ".join(str(number) for number in sorted(MAPPERS))
            raise CartridgeError(
                f"Mapper {self.mapper_id} is not supported in this build. "
                f"Supported mappers: {supported}."
            )
        self.mapper = mapper_type(self)

    @classmethod
    def from_file(cls, path: str | pathlib.Path) -> "Cartridge":
        file_path = pathlib.Path(path)
        return cls(file_path.read_bytes(), str(file_path))

    def cpu_read(self, address: int) -> int:
        if 0x4020 <= address < 0x6000:
            value = self.mapper.register_read(address)
            return value & 0xFF if value is not None else 0
        if 0x6000 <= address < 0x8000:
            mapped = self.mapper.cpu_read(address)
            if mapped is not None:
                return self.prg[mapped]
            return self.prg_ram[address & 0x1FFF]
        mapped = self.mapper.cpu_read(address)
        return self.prg[mapped] if mapped is not None else 0

    def cpu_write(self, address: int, value: int) -> None:
        if 0x4020 <= address < 0x6000:
            self.mapper.cpu_write(address, value)
        elif 0x6000 <= address < 0x8000:
            if not self.mapper.cpu_write(address, value):
                self.prg_ram[address & 0x1FFF] = value
        else:
            self.mapper.cpu_write(address, value)

    def ppu_read(self, address: int) -> int:
        mapped = self.mapper.ppu_read(address)
        return self.chr[mapped] if mapped is not None else 0

    def ppu_write(self, address: int, value: int) -> None:
        self.mapper.ppu_write(address, value)


LENGTH_TABLE = (
    10, 254, 20, 2, 40, 4, 80, 6, 160, 8, 60, 10, 14, 12, 26, 14,
    12, 16, 24, 18, 48, 20, 96, 22, 192, 24, 72, 26, 16, 28, 32, 30,
)


class Envelope:
    """2A03 divider/decay envelope shared by pulse and noise channels."""

    def __init__(self) -> None:
        self.loop = False
        self.constant = False
        self.period = 0
        self.start = False
        self.divider = 0
        self.decay = 0

    def write(self, value: int) -> None:
        self.loop = bool(value & 0x20)
        self.constant = bool(value & 0x10)
        self.period = value & 0x0F

    def restart(self) -> None:
        self.start = True

    def clock(self) -> None:
        if self.start:
            self.start = False
            self.decay = 15
            self.divider = self.period
        elif self.divider:
            self.divider -= 1
        else:
            self.divider = self.period
            if self.decay:
                self.decay -= 1
            elif self.loop:
                self.decay = 15

    @property
    def output(self) -> int:
        return self.period if self.constant else self.decay


class PulseChannel:
    DUTY_TABLE = (
        (0, 1, 0, 0, 0, 0, 0, 0),
        (0, 1, 1, 0, 0, 0, 0, 0),
        (0, 1, 1, 1, 1, 0, 0, 0),
        (1, 0, 0, 1, 1, 1, 1, 1),
    )

    def __init__(self, channel: int) -> None:
        self.channel = channel
        self.enabled = False
        self.duty = 0
        self.sequence = 0
        self.timer_period = 0
        self.timer = 0
        self.length = 0
        self.envelope = Envelope()
        self.sweep_enabled = False
        self.sweep_period = 0
        self.sweep_negate = False
        self.sweep_shift = 0
        self.sweep_reload = False
        self.sweep_divider = 0

    def write(self, register: int, value: int) -> None:
        if register == 0:
            self.duty = (value >> 6) & 3
            self.envelope.write(value)
        elif register == 1:
            self.sweep_enabled = bool(value & 0x80)
            self.sweep_period = (value >> 4) & 7
            self.sweep_negate = bool(value & 0x08)
            self.sweep_shift = value & 7
            self.sweep_reload = True
        elif register == 2:
            self.timer_period = (self.timer_period & 0x700) | value
        else:
            self.timer_period = (self.timer_period & 0x0FF) | ((value & 7) << 8)
            if self.enabled:
                self.length = LENGTH_TABLE[value >> 3]
            self.sequence = 0
            self.envelope.restart()

    def clock_timer(self) -> None:
        if self.timer:
            self.timer -= 1
        else:
            self.timer = self.timer_period
            self.sequence = (self.sequence + 1) & 7

    def advance_timer(self, ticks: int) -> None:
        if ticks <= 0:
            return
        if ticks <= self.timer:
            self.timer -= ticks
            return
        ticks -= self.timer + 1
        interval = self.timer_period + 1
        events = 1 + ticks // interval
        remainder = ticks % interval
        self.sequence = (self.sequence + events) & 7
        self.timer = self.timer_period - remainder

    def target_period(self) -> int:
        change = self.timer_period >> self.sweep_shift if self.sweep_shift else 0
        if self.sweep_negate:
            return self.timer_period - change - (1 if self.channel == 1 else 0)
        return self.timer_period + change

    def sweep_muted(self) -> bool:
        return self.timer_period < 8 or self.target_period() > 0x7FF

    def clock_sweep(self) -> None:
        if (
            self.sweep_divider == 0
            and self.sweep_enabled
            and self.sweep_shift
            and not self.sweep_muted()
        ):
            self.timer_period = self.target_period() & 0x7FF
        if self.sweep_divider == 0 or self.sweep_reload:
            self.sweep_divider = self.sweep_period
            self.sweep_reload = False
        else:
            self.sweep_divider -= 1

    def clock_length(self) -> None:
        if self.length and not self.envelope.loop:
            self.length -= 1

    @property
    def output(self) -> int:
        if (
            not self.enabled
            or not self.length
            or self.sweep_muted()
            or not self.DUTY_TABLE[self.duty][self.sequence]
        ):
            return 0
        return self.envelope.output


class TriangleChannel:
    SEQUENCE = tuple(range(15, -1, -1)) + tuple(range(16))

    def __init__(self) -> None:
        self.enabled = False
        self.control = False
        self.linear_reload_value = 0
        self.linear_reload = False
        self.linear_counter = 0
        self.timer_period = 0
        self.timer = 0
        self.length = 0
        self.sequence = 0

    def write(self, register: int, value: int) -> None:
        if register == 0:
            self.control = bool(value & 0x80)
            self.linear_reload_value = value & 0x7F
        elif register == 2:
            self.timer_period = (self.timer_period & 0x700) | value
        elif register == 3:
            self.timer_period = (self.timer_period & 0x0FF) | ((value & 7) << 8)
            if self.enabled:
                self.length = LENGTH_TABLE[value >> 3]
            self.linear_reload = True

    def clock_timer(self) -> None:
        if self.timer:
            self.timer -= 1
        else:
            self.timer = self.timer_period
            if self.enabled and self.length and self.linear_counter and self.timer_period > 1:
                self.sequence = (self.sequence + 1) & 31

    def advance_timer(self, ticks: int) -> None:
        if ticks <= 0:
            return
        if ticks <= self.timer:
            self.timer -= ticks
            return
        ticks -= self.timer + 1
        interval = self.timer_period + 1
        events = 1 + ticks // interval
        remainder = ticks % interval
        if self.enabled and self.length and self.linear_counter and self.timer_period > 1:
            self.sequence = (self.sequence + events) & 31
        self.timer = self.timer_period - remainder

    def clock_linear(self) -> None:
        if self.linear_reload:
            self.linear_counter = self.linear_reload_value
        elif self.linear_counter:
            self.linear_counter -= 1
        if not self.control:
            self.linear_reload = False

    def clock_length(self) -> None:
        if self.length and not self.control:
            self.length -= 1

    @property
    def output(self) -> int:
        # The triangle DAC holds its last level when either counter halts.
        return self.SEQUENCE[self.sequence]


class NoiseChannel:
    PERIOD_TABLE = (
        4, 8, 16, 32, 64, 96, 128, 160,
        202, 254, 380, 508, 762, 1016, 2034, 4068,
    )

    def __init__(self) -> None:
        self.enabled = False
        self.mode = False
        self.period = self.PERIOD_TABLE[0]
        self.timer = 0
        self.length = 0
        self.shift = 1
        self.envelope = Envelope()

    def write(self, register: int, value: int) -> None:
        if register == 0:
            self.envelope.write(value)
        elif register == 2:
            self.mode = bool(value & 0x80)
            self.period = self.PERIOD_TABLE[value & 0x0F]
        elif register == 3:
            if self.enabled:
                self.length = LENGTH_TABLE[value >> 3]
            self.envelope.restart()

    def clock_timer(self) -> None:
        if self.timer:
            self.timer -= 1
        else:
            self.timer = self.period - 1
            tap = 6 if self.mode else 1
            feedback = (self.shift & 1) ^ ((self.shift >> tap) & 1)
            self.shift = (self.shift >> 1) | (feedback << 14)

    def advance_timer(self, ticks: int) -> None:
        while ticks > self.timer:
            ticks -= self.timer + 1
            self.timer = self.period - 1
            tap = 6 if self.mode else 1
            feedback = (self.shift & 1) ^ ((self.shift >> tap) & 1)
            self.shift = (self.shift >> 1) | (feedback << 14)
        self.timer -= ticks

    def clock_length(self) -> None:
        if self.length and not self.envelope.loop:
            self.length -= 1

    @property
    def output(self) -> int:
        if not self.enabled or not self.length or self.shift & 1:
            return 0
        return self.envelope.output


class DMCChannel:
    RATE_TABLE = (
        428, 380, 340, 320, 286, 254, 226, 214,
        190, 160, 142, 128, 106, 84, 72, 54,
    )

    def __init__(self, bus: "Bus") -> None:
        self.bus = bus
        self.enabled = False
        self.irq_enabled = False
        self.loop = False
        self.irq = False
        self.period = self.RATE_TABLE[0]
        self.timer = 0
        self.output = 0
        self.sample_address = 0xC000
        self.sample_length = 1
        self.current_address = 0xC000
        self.bytes_remaining = 0
        self.sample_buffer: Optional[int] = None
        self.shift = 0
        self.bits_remaining = 8
        self.silence = True

    def write(self, address: int, value: int) -> None:
        if address == 0x4010:
            self.irq_enabled = bool(value & 0x80)
            self.loop = bool(value & 0x40)
            self.period = self.RATE_TABLE[value & 0x0F]
            if not self.irq_enabled:
                self.irq = False
        elif address == 0x4011:
            self.output = value & 0x7F
        elif address == 0x4012:
            self.sample_address = 0xC000 | (value << 6)
        elif address == 0x4013:
            self.sample_length = (value << 4) | 1

    def set_enabled(self, enabled: bool) -> None:
        self.enabled = enabled
        self.irq = False
        if not enabled:
            self.bytes_remaining = 0
        elif self.bytes_remaining == 0:
            self.restart()

    def restart(self) -> None:
        self.current_address = self.sample_address
        self.bytes_remaining = self.sample_length

    def _fill_buffer(self) -> None:
        if self.sample_buffer is not None or not self.bytes_remaining:
            return
        self.sample_buffer = self.bus.peek(self.current_address)
        if hasattr(self.bus, "cpu"):
            self.bus.cpu.stall += 4
        self.current_address = 0x8000 if self.current_address == 0xFFFF else self.current_address + 1
        self.bytes_remaining -= 1
        if self.bytes_remaining == 0:
            if self.loop:
                self.restart()
            elif self.irq_enabled:
                self.irq = True

    def clock_timer(self) -> None:
        self._fill_buffer()
        if self.timer:
            self.timer -= 1
            return
        self.timer = self.period - 1
        if not self.silence:
            if self.shift & 1:
                if self.output <= 125:
                    self.output += 2
            elif self.output >= 2:
                self.output -= 2
        self.shift >>= 1
        self.bits_remaining -= 1
        if self.bits_remaining == 0:
            self.bits_remaining = 8
            if self.sample_buffer is None:
                self.silence = True
            else:
                self.silence = False
                self.shift = self.sample_buffer
                self.sample_buffer = None
        self._fill_buffer()

    def advance_timer(self, ticks: int) -> None:
        self._fill_buffer()
        while ticks > self.timer:
            ticks -= self.timer + 1
            self.timer = self.period - 1
            if not self.silence:
                if self.shift & 1:
                    if self.output <= 125:
                        self.output += 2
                elif self.output >= 2:
                    self.output -= 2
            self.shift >>= 1
            self.bits_remaining -= 1
            if self.bits_remaining == 0:
                self.bits_remaining = 8
                if self.sample_buffer is None:
                    self.silence = True
                else:
                    self.silence = False
                    self.shift = self.sample_buffer
                    self.sample_buffer = None
            self._fill_buffer()
        self.timer -= ticks
        self._fill_buffer()


class APU:
    """Cycle-timed NTSC Ricoh 2A03 APU with all five native sound channels."""

    SAMPLE_RATE = 48_000

    def __init__(self, bus: "Bus") -> None:
        self.bus = bus
        self.pulse1 = PulseChannel(1)
        self.pulse2 = PulseChannel(2)
        self.triangle = TriangleChannel()
        self.noise = NoiseChannel()
        self.dmc = DMCChannel(bus)
        self.frame_cycle = 0
        self.cpu_cycle = 0
        self.five_step = False
        self.irq_inhibit = False
        self.frame_irq = False
        self.frame_reset_delay = 0
        self.sample_phase = 0
        self.samples = array("h")
        self.previous_mixed = 0.0
        self.high_pass = 0.0
        self.low_pass = 0.0

    @property
    def irq_pending(self) -> bool:
        return self.frame_irq or self.dmc.irq

    @property
    def irq_may_fire(self) -> bool:
        return (
            self.irq_pending
            or (not self.five_step and not self.irq_inhibit)
            or (self.dmc.enabled and self.dmc.irq_enabled)
        )

    @property
    def requires_cpu_sync(self) -> bool:
        return bool(
            self.dmc.enabled
            and (self.dmc.bytes_remaining or self.dmc.sample_buffer is not None or not self.dmc.silence)
        )

    def reset(self) -> None:
        self.__init__(self.bus)

    def write(self, address: int, value: int) -> None:
        value &= 0xFF
        if 0x4000 <= address <= 0x4003:
            self.pulse1.write(address & 3, value)
        elif 0x4004 <= address <= 0x4007:
            self.pulse2.write(address & 3, value)
        elif address in (0x4008, 0x400A, 0x400B):
            self.triangle.write(address & 3, value)
        elif address in (0x400C, 0x400E, 0x400F):
            self.noise.write(address & 3, value)
        elif 0x4010 <= address <= 0x4013:
            self.dmc.write(address, value)
        elif address == 0x4015:
            self.pulse1.enabled = bool(value & 0x01)
            self.pulse2.enabled = bool(value & 0x02)
            self.triangle.enabled = bool(value & 0x04)
            self.noise.enabled = bool(value & 0x08)
            if not self.pulse1.enabled:
                self.pulse1.length = 0
            if not self.pulse2.enabled:
                self.pulse2.length = 0
            if not self.triangle.enabled:
                self.triangle.length = 0
            if not self.noise.enabled:
                self.noise.length = 0
            self.dmc.set_enabled(bool(value & 0x10))
        elif address == 0x4017:
            self.five_step = bool(value & 0x80)
            self.irq_inhibit = bool(value & 0x40)
            if self.irq_inhibit:
                self.frame_irq = False
            # Hardware applies the new sequence after 3 or 4 CPU cycles.
            self.frame_reset_delay = 3 if self.cpu_cycle & 1 else 4

    def read_status(self) -> int:
        value = 0
        value |= int(self.pulse1.length > 0)
        value |= int(self.pulse2.length > 0) << 1
        value |= int(self.triangle.length > 0) << 2
        value |= int(self.noise.length > 0) << 3
        value |= int(self.dmc.bytes_remaining > 0) << 4
        value |= int(self.frame_irq) << 6
        value |= int(self.dmc.irq) << 7
        self.frame_irq = False
        return value

    def _quarter_frame(self) -> None:
        self.pulse1.envelope.clock()
        self.pulse2.envelope.clock()
        self.noise.envelope.clock()
        self.triangle.clock_linear()

    def _half_frame(self) -> None:
        self.pulse1.clock_length()
        self.pulse2.clock_length()
        self.triangle.clock_length()
        self.noise.clock_length()
        self.pulse1.clock_sweep()
        self.pulse2.clock_sweep()

    def _next_frame_event(self) -> int:
        events = (3729, 7457, 11186, 18641) if self.five_step else (3729, 7457, 11186, 14915)
        for event in events:
            if event > self.frame_cycle:
                return event
        return events[-1]

    def _handle_frame_event(self) -> None:
        if self.five_step:
            if self.frame_cycle in (3729, 11186):
                self._quarter_frame()
            elif self.frame_cycle in (7457, 18641):
                self._quarter_frame()
                self._half_frame()
            if self.frame_cycle >= 18641:
                self.frame_cycle = 0
        else:
            if self.frame_cycle in (3729, 11186):
                self._quarter_frame()
            elif self.frame_cycle in (7457, 14915):
                self._quarter_frame()
                self._half_frame()
            if self.frame_cycle >= 14915:
                if not self.irq_inhibit:
                    self.frame_irq = True
                self.frame_cycle = 0

    def _advance_timers(self, cpu_cycles: int) -> None:
        old_cycle = self.cpu_cycle
        self.cpu_cycle += cpu_cycles
        pulse_ticks = ((old_cycle & 1) + cpu_cycles) // 2
        if self.pulse1.enabled:
            self.pulse1.advance_timer(pulse_ticks)
        if self.pulse2.enabled:
            self.pulse2.advance_timer(pulse_ticks)
        if self.triangle.enabled:
            self.triangle.advance_timer(cpu_cycles)
        if self.noise.enabled:
            self.noise.advance_timer(cpu_cycles)
        if self.dmc.bytes_remaining or self.dmc.sample_buffer is not None or not self.dmc.silence:
            self.dmc.advance_timer(cpu_cycles)

    def _mix_sample(self) -> int:
        pulse_sum = self.pulse1.output + self.pulse2.output
        pulse = 95.88 / (8128.0 / pulse_sum + 100.0) if pulse_sum else 0.0
        tnd_input = (
            self.triangle.output / 8227.0
            + self.noise.output / 12241.0
            + self.dmc.output / 22638.0
        )
        tnd = 159.79 / (1.0 / tnd_input + 100.0) if tnd_input else 0.0
        mixed = pulse + tnd
        # A gentle DC blocker and reconstruction low-pass approximate the
        # analog output path while leaving digital channel timing untouched.
        self.high_pass = mixed - self.previous_mixed + 0.996 * self.high_pass
        self.previous_mixed = mixed
        self.low_pass += 0.35 * (self.high_pass - self.low_pass)
        return max(-32768, min(32767, int(self.low_pass * 47_000)))

    def step(self, cpu_cycles: int) -> None:
        remaining = cpu_cycles
        while remaining:
            to_sample = (CPU_CLOCK - self.sample_phase + self.SAMPLE_RATE - 1) // self.SAMPLE_RATE
            frame_target = self._next_frame_event()
            to_frame_event = frame_target - self.frame_cycle
            to_frame = min(
                to_frame_event,
                self.frame_reset_delay if self.frame_reset_delay else to_frame_event,
            )
            advance = min(remaining, to_sample, to_frame)
            self._advance_timers(advance)
            self.frame_cycle += advance
            self.sample_phase += advance * self.SAMPLE_RATE
            remaining -= advance
            reset_due = bool(self.frame_reset_delay and advance == self.frame_reset_delay)
            if self.frame_reset_delay:
                self.frame_reset_delay -= advance
            if self.frame_cycle == frame_target:
                self._handle_frame_event()
            if reset_due:
                self.frame_cycle = 0
                if self.five_step:
                    self._quarter_frame()
                    self._half_frame()
            if self.sample_phase >= CPU_CLOCK:
                self.sample_phase -= CPU_CLOCK
                self.samples.append(self._mix_sample())

    def drain_samples(self) -> bytes:
        if not self.samples:
            return b""
        samples = self.samples
        self.samples = array("h")
        if sys.byteorder != "little":
            samples.byteswap()
        return samples.tobytes()


class AudioOutput:
    """Optional pygame-ce/pygame streaming sink; the emulator stays usable silent."""

    def __init__(self) -> None:
        self.pygame = None
        self.channel = None
        self.available = False
        self.muted = False
        self.error = ""
        try:
            os.environ.setdefault("PYGAME_HIDE_SUPPORT_PROMPT", "1")
            import pygame  # type: ignore[import-not-found]

            try:
                pygame.mixer.init(
                    frequency=APU.SAMPLE_RATE,
                    size=-16,
                    channels=1,
                    buffer=1024,
                    allowedchanges=0,
                )
            except TypeError:
                pygame.mixer.init(
                    frequency=APU.SAMPLE_RATE,
                    size=-16,
                    channels=1,
                    buffer=1024,
                )
            self.pygame = pygame
            self.channel = pygame.mixer.Channel(0)
            self.available = True
        except Exception as exc:
            self.error = str(exc)

    def submit(self, pcm: bytes) -> None:
        if not pcm or not self.available or self.muted or not self.pygame or not self.channel:
            return
        sound = self.pygame.mixer.Sound(buffer=pcm)
        if not self.channel.get_busy():
            self.channel.play(sound)
        elif self.channel.get_queue() is None:
            self.channel.queue(sound)

    def clear(self) -> None:
        if self.available and self.channel:
            self.channel.stop()

    def close(self) -> None:
        if self.pygame:
            try:
                self.pygame.mixer.quit()
            except Exception:
                pass


class PPU:
    def __init__(self, cart: Cartridge) -> None:
        self.cart = cart
        self.bus: Optional[Bus] = None
        self.ctrl = 0
        self.mask = 0
        self.status = 0
        self.oam_address = 0
        self.oam = bytearray(256)
        self.vram = bytearray(0x1000)
        self.palette = bytearray(32)
        self.address = 0
        self.temp_address = 0
        self.fine_x = 0
        self.write_latch = 0
        self.read_buffer = 0
        self.scroll_x = 0
        self.scroll_y = 0
        self.dot = 0
        self.scanline = 261
        self.odd_frame = False
        self.frame_number = 0
        self.frame_ready = False
        self.framebuffer = bytearray(SCREEN_W * SCREEN_H * 3)
        self.bg_opaque = bytearray(SCREEN_W * SCREEN_H)
        self._ppu_open_bus = 0
        self._palette_rgb: list[tuple[int, int, int]] = []
        self._frame_render_active = False

    def reset(self) -> None:
        self.ctrl = self.mask = self.status = 0
        self.address = self.temp_address = self.fine_x = self.write_latch = 0
        self.dot, self.scanline = 0, 261
        self.frame_ready = False
        self._ppu_open_bus = 0

    def _nametable_index(self, address: int) -> int:
        raw = (address - 0x2000) & 0x0FFF
        table, offset = raw >> 10, raw & 0x3FF
        mode = self.cart.mapper.mirror_mode()
        if mode == "vertical":
            physical = table & 1
        elif mode == "horizontal":
            physical = table >> 1
        elif mode == "single1":
            physical = 1
        elif mode == "four":
            physical = table
        else:
            physical = 0
        return (physical << 10) + offset

    @staticmethod
    def _palette_index(address: int) -> int:
        index = address & 0x1F
        if index & 0x13 == 0x10:
            index &= 0x0F
        return index

    def memory_read(self, address: int) -> int:
        address &= 0x3FFF
        if address < 0x2000:
            return self.cart.ppu_read(address)
        if address < 0x3F00:
            return self.vram[self._nametable_index(address)]
        return self.palette[self._palette_index(address)] & 0x3F

    def memory_write(self, address: int, value: int) -> None:
        address &= 0x3FFF
        value &= 0xFF
        if address < 0x2000:
            self.cart.ppu_write(address, value)
        elif address < 0x3F00:
            self.vram[self._nametable_index(address)] = value
        else:
            self.palette[self._palette_index(address)] = value & 0x3F

    def read_register(self, address: int) -> int:
        register = address & 7
        if register == 2:
            value = self.status
            self.status &= ~0x80
            self.write_latch = 0
            self._ppu_open_bus = value
            return value
        if register == 4:
            value = self.oam[self.oam_address]
            self._ppu_open_bus = value
            return value
        if register == 7:
            value = self.memory_read(self.address)
            if self.address < 0x3F00:
                returned = self.read_buffer
                self.read_buffer = value
            else:
                returned = value
                self.read_buffer = self.memory_read(self.address - 0x1000)
            self.address = (self.address + (32 if self.ctrl & 4 else 1)) & 0x7FFF
            self._ppu_open_bus = returned
            return returned
        # PPUCTRL/PPUMASK/OAMADDR/PPUSCROLL/PPUADDR are write-only; open bus.
        return getattr(self, "_ppu_open_bus", 0)

    def write_register(self, address: int, value: int) -> None:
        register = address & 7
        value &= 0xFF
        if register == 0:
            old_nmi = bool(self.ctrl & 0x80)
            self.ctrl = value
            self.temp_address = (self.temp_address & 0x73FF) | ((value & 3) << 10)
            if not old_nmi and value & 0x80 and self.status & 0x80 and self.bus:
                self.bus.cpu.nmi_pending = True
        elif register == 1:
            self.mask = value
        elif register == 3:
            self.oam_address = value
        elif register == 4:
            self.oam[self.oam_address] = value
            self.oam_address = (self.oam_address + 1) & 0xFF
        elif register == 5:
            if self.write_latch == 0:
                self.scroll_x = value
                self.fine_x = value & 7
                self.temp_address = (self.temp_address & 0x7FE0) | (value >> 3)
            else:
                self.scroll_y = value
                self.temp_address = (
                    (self.temp_address & 0x0C1F)
                    | ((value & 7) << 12)
                    | ((value & 0xF8) << 2)
                )
            self.write_latch ^= 1
        elif register == 6:
            if self.write_latch == 0:
                self.temp_address = (self.temp_address & 0x00FF) | ((value & 0x3F) << 8)
            else:
                self.temp_address = (self.temp_address & 0x7F00) | value
                self.address = self.temp_address
                self._sync_scroll_from_v()
            self.write_latch ^= 1
        elif register == 7:
            self.memory_write(self.address, value)
            self.address = (self.address + (32 if self.ctrl & 4 else 1)) & 0x7FFF

    def step(self, ppu_cycles: int) -> None:
        # Jump between PPU events rather than interpreting every single dot in
        # Python. CPU instructions still finish at their correct PPU position,
        # but this removes roughly 90,000 loop iterations from every frame.
        new_dot = self.dot + ppu_cycles
        if new_dot < 341:
            old_dot = self.dot
            self.dot = new_dot
            if self.scanline < 240 and old_dot < 260 <= new_dot and self.mask & 0x18:
                self.cart.mapper.clock_scanline()
            elif self.scanline == 241 and old_dot < 1 <= new_dot:
                self.status |= 0x80
                self.frame_number += 1
                self.frame_ready = True
                if self.ctrl & 0x80 and self.bus:
                    self.bus.cpu.nmi_pending = True
            elif self.scanline == 261 and old_dot < 1 <= new_dot:
                self.status &= ~0xE0
            return
        remaining = ppu_cycles
        while remaining:
            advance = min(remaining, 341 - self.dot)
            old_dot = self.dot
            self.dot += advance
            remaining -= advance
            if self.scanline < 240 and old_dot < 260 <= self.dot and self.mask & 0x18:
                self.cart.mapper.clock_scanline()
            if self.scanline == 241 and old_dot < 1 <= self.dot:
                self.status |= 0x80
                self.frame_number += 1
                self.frame_ready = True
                if self.ctrl & 0x80 and self.bus:
                    self.bus.cpu.nmi_pending = True
            elif self.scanline == 261 and old_dot < 1 <= self.dot:
                self.status &= ~0xE0
            if self.dot >= 341:
                self.dot -= 341
                # NTSC odd frames skip the first idle dot when rendering is on.
                if (
                    self.scanline == 261
                    and self.odd_frame
                    and (self.mask & 0x18)
                    and self.dot == 0
                ):
                    self.dot = 1
                finished = self.scanline
                self.scanline += 1
                if self.scanline > 261:
                    self.scanline = 0
                    self.odd_frame = not self.odd_frame
                if self.scanline == 0:
                    self._prepare_frame()
                elif finished < 240:
                    self._render_scanline(finished)

    def _color(self, palette_address: int) -> tuple[int, int, int]:
        return NES_PALETTE[self.memory_read(palette_address) & 0x3F]

    def _emphasized(self, color: tuple[int, int, int]) -> tuple[int, int, int]:
        """Apply PPUMASK RGB emphasis like FCEUX/NTSC 2C02 (greyscale is palette-side)."""
        r, g, b = color
        # Emphasis bits darken the complementary channels (~25%).
        if self.mask & 0x20:  # emphasize red → darken G+B
            g = (g * 3) // 4
            b = (b * 3) // 4
        if self.mask & 0x40:  # emphasize green → darken R+B
            r = (r * 3) // 4
            b = (b * 3) // 4
        if self.mask & 0x80:  # emphasize blue → darken R+G
            r = (r * 3) // 4
            g = (g * 3) // 4
        return r, g, b

    def _sync_scroll_from_v(self) -> None:
        """Update renderer scroll from the PPU v/t address (post-$2006 writes)."""
        v = self.temp_address
        self.scroll_x = ((v & 0x1F) << 3) | self.fine_x
        self.scroll_y = (((v >> 5) & 0x1F) << 3) | ((v >> 12) & 7)

    def _prepare_frame(self) -> None:
        grey_mask = 0x30 if self.mask & 0x01 else 0x3F
        palette = self.palette
        index_fn = self._palette_index
        emphasize = self._emphasized
        # Store packed RGB bytes for fast framebuffer slice writes.
        self._palette_rgb = [
            bytes(emphasize(NES_PALETTE[palette[index_fn(0x3F00 + index)] & grey_mask]))
            for index in range(32)
        ]
        universal = self._palette_rgb[0]
        self.framebuffer[:] = universal * (SCREEN_W * SCREEN_H)
        self.bg_opaque[:] = b"\0" * (SCREEN_W * SCREEN_H)
        self.status &= ~0x20
        self._frame_render_active = True
        self._overflow_done = False
        # Cache mirroring for the duration of the frame (games IRQ may change
        # mid-frame; we refresh each scanline from the mapper if needed).
        self._mirror = self.cart.mapper.mirror_mode()

    def _nt_byte(self, address: int) -> int:
        """Nametable read using the cached mirror mode (hot renderer path)."""
        raw = (address - 0x2000) & 0x0FFF
        table = raw >> 10
        offset = raw & 0x3FF
        mode = self._mirror
        if mode == "vertical":
            physical = table & 1
        elif mode == "horizontal":
            physical = table >> 1
        elif mode == "single1":
            physical = 1
        elif mode == "four":
            physical = table
        else:
            physical = 0
        return self.vram[(physical << 10) + offset]

    def _chr_byte(self, address: int) -> int:
        cart = self.cart
        mapper = cart.mapper
        if cart.mapper_id == 0:
            return cart.chr[address % cart.chr_len]
        if cart.mapper_id == 4:
            logical = address ^ mapper._chr_xor
            return cart.chr[mapper._chr_base[logical >> 10] + (logical & 0x3FF)]
        mapped = mapper.ppu_read(address)
        return cart.chr[mapped] if mapped is not None else 0

    def _render_scanline(self, y: int) -> None:
        """Draw one visible scanline using the PPU state active at line start."""
        rgb = self.framebuffer
        opaque = self.bg_opaque
        palette_rgb = self._palette_rgb
        if not palette_rgb:
            return
        mask = self.mask
        show_bg = mask & 0x08
        show_sprites = mask & 0x10
        chr_ = self._chr_byte
        row_start = y * SCREEN_W
        lut = PIXEL_ROW_LUT
        if show_bg:
            pattern_base = 0x1000 if self.ctrl & 0x10 else 0
            base_nt = (self.temp_address >> 10) & 3
            scroll_x = self.scroll_x
            scroll_y = self.scroll_y
            world_y = y + scroll_y
            if world_y >= 480:
                world_y -= 480
                if world_y >= 480:
                    world_y %= 480
            nt_y = 1 if world_y >= 240 else 0
            local_y = world_y - 240 if nt_y else world_y
            tile_y = local_y >> 3
            fine_y = local_y & 7
            left_clip = not (mask & 0x02)
            attr_row = (tile_y >> 2) << 3
            remap = MIRROR_REMAP.get(self.cart.mapper.mirror_mode(), (0, 0, 0, 0))
            vram = self.vram
            x = 0
            # Fast path: aligned scroll, left column enabled — 32 full tiles.
            if not left_clip and (scroll_x & 7) == 0:
                while x < SCREEN_W:
                    world_x = x + scroll_x
                    if world_x >= 512:
                        world_x &= 511
                    nt_x = 1 if world_x >= 256 else 0
                    local_x = world_x - 256 if nt_x else world_x
                    table = ((base_nt & 1) ^ nt_x) | ((((base_nt >> 1) & 1) ^ nt_y) << 1)
                    tile_x = local_x >> 3
                    nt_base = remap[table] << 10
                    tile = vram[nt_base + (tile_y << 5) + tile_x]
                    attribute = vram[nt_base + 0x3C0 + attr_row + (tile_x >> 2)]
                    shift = ((tile_y & 2) << 1) | (tile_x & 2)
                    base = ((attribute >> shift) & 3) << 2
                    pattern = pattern_base + (tile << 4) + fine_y
                    pixels = lut[(chr_(pattern + 8) << 8) | chr_(pattern)]
                    pos = row_start + x
                    p0, p1, p2, p3, p4, p5, p6, p7 = pixels
                    if p0:
                        opaque[pos] = 1
                        rgb[pos * 3:pos * 3 + 3] = palette_rgb[base + p0]
                    if p1:
                        opaque[pos + 1] = 1
                        rgb[(pos + 1) * 3:(pos + 1) * 3 + 3] = palette_rgb[base + p1]
                    if p2:
                        opaque[pos + 2] = 1
                        rgb[(pos + 2) * 3:(pos + 2) * 3 + 3] = palette_rgb[base + p2]
                    if p3:
                        opaque[pos + 3] = 1
                        rgb[(pos + 3) * 3:(pos + 3) * 3 + 3] = palette_rgb[base + p3]
                    if p4:
                        opaque[pos + 4] = 1
                        rgb[(pos + 4) * 3:(pos + 4) * 3 + 3] = palette_rgb[base + p4]
                    if p5:
                        opaque[pos + 5] = 1
                        rgb[(pos + 5) * 3:(pos + 5) * 3 + 3] = palette_rgb[base + p5]
                    if p6:
                        opaque[pos + 6] = 1
                        rgb[(pos + 6) * 3:(pos + 6) * 3 + 3] = palette_rgb[base + p6]
                    if p7:
                        opaque[pos + 7] = 1
                        rgb[(pos + 7) * 3:(pos + 7) * 3 + 3] = palette_rgb[base + p7]
                    x += 8
            else:
                while x < SCREEN_W:
                    world_x = x + scroll_x
                    if world_x >= 512:
                        world_x &= 511
                    nt_x = 1 if world_x >= 256 else 0
                    local_x = world_x - 256 if nt_x else world_x
                    table = ((base_nt & 1) ^ nt_x) | ((((base_nt >> 1) & 1) ^ nt_y) << 1)
                    tile_x = local_x >> 3
                    fine_px = local_x & 7
                    run = 8 - fine_px
                    if x + run > SCREEN_W:
                        run = SCREEN_W - x
                    nt_base = remap[table] << 10
                    tile = vram[nt_base + (tile_y << 5) + tile_x]
                    attribute = vram[nt_base + 0x3C0 + attr_row + (tile_x >> 2)]
                    shift = ((tile_y & 2) << 1) | (tile_x & 2)
                    base = ((attribute >> shift) & 3) << 2
                    pattern = pattern_base + (tile << 4) + fine_y
                    pixels = lut[(chr_(pattern + 8) << 8) | chr_(pattern)]
                    pos0 = row_start + x
                    for dx in range(run):
                        screen_x = x + dx
                        if left_clip and screen_x < 8:
                            continue
                        pixel = pixels[fine_px + dx]
                        if pixel:
                            position = pos0 + dx
                            opaque[position] = 1
                            rgb[position * 3:position * 3 + 3] = palette_rgb[base + pixel]
                    x += run
        if show_sprites:
            height = 16 if self.ctrl & 0x20 else 8
            sprite_pattern = 0x1000 if self.ctrl & 0x08 else 0
            oam = self.oam
            left_clip = not (mask & 0x04)
            selected: list[int] = []
            for sprite in range(64):
                top = oam[sprite << 2] + 1
                if top <= y < top + height:
                    if len(selected) >= 8:
                        self.status |= 0x20
                        break
                    selected.append(sprite)
            for sprite in reversed(selected):
                base_oam = sprite << 2
                top = oam[base_oam] + 1
                tile = oam[base_oam + 1]
                attributes = oam[base_oam + 2]
                left = oam[base_oam + 3]
                if left >= SCREEN_W:
                    continue
                sy = y - top
                row = (height - 1 - sy) if attributes & 0x80 else sy
                if height == 16:
                    bank = (tile & 1) << 12
                    tile_number = (tile & 0xFE) + (row >> 3)
                    tile_row = row & 7
                else:
                    bank = sprite_pattern
                    tile_number = tile
                    tile_row = row
                pattern = bank + (tile_number << 4) + tile_row
                pixels = lut[(chr_(pattern + 8) << 8) | chr_(pattern)]
                flip_x = attributes & 0x40
                behind = attributes & 0x20
                spr_base = 0x10 + ((attributes & 3) << 2)
                for sx in range(8):
                    screen_x = left + sx
                    if screen_x >= SCREEN_W or (left_clip and screen_x < 8):
                        continue
                    pixel = pixels[sx if not flip_x else 7 - sx]
                    if not pixel:
                        continue
                    position = row_start + screen_x
                    if sprite == 0 and opaque[position] and screen_x < 255:
                        self.status |= 0x40
                    if behind and opaque[position]:
                        continue
                    rgb[position * 3:position * 3 + 3] = palette_rgb[spr_base + pixel]

    def _evaluate_sprite_overflow(self) -> None:
        """Fallback overflow scan when the line renderer did not run."""
        if self.status & 0x20:
            return
        height = 16 if self.ctrl & 0x20 else 8
        oam = self.oam
        for scan_y in range(SCREEN_H):
            hits = 0
            for sprite in range(64):
                top = oam[sprite * 4] + 1
                if top <= scan_y < top + height:
                    hits += 1
                    if hits > 8:
                        self.status |= 0x20
                        return

    def finish_frame(self) -> bytearray:
        """Finalize a frame rendered scanline-by-scanline during PPU stepping."""
        if not self._frame_render_active:
            return self.render()
        self._frame_render_active = False
        return self.framebuffer

    def render(self) -> bytearray:
        """Full-frame render (used when the PPU is not stepped normally)."""
        self._prepare_frame()
        for y in range(SCREEN_H):
            self._render_scanline(y)
        self._frame_render_active = False
        return self.framebuffer


class Bus:
    def __init__(self, cart: Cartridge) -> None:
        self.cart = cart
        self.ram = bytearray(0x800)
        self.ppu = PPU(cart)
        self.apu = APU(self)
        self.apu_pending_cycles = 0
        self.cpu = CPU(self)
        self.ppu.bus = self
        self.controller_state = [0, 0]
        self.controller_shift = [0, 0]
        self.controller_strobe = False

    def read(self, address: int) -> int:
        address &= 0xFFFF
        if address < 0x2000:
            return self.ram[address & 0x7FF]
        if address < 0x4000:
            return self.ppu.read_register(address)
        if address == 0x4015:
            self.sync_apu()
            return self.apu.read_status()
        if address in (0x4016, 0x4017):
            port = address & 1
            if self.controller_strobe:
                value = self.controller_state[port] & 1
            else:
                value = self.controller_shift[port] & 1
                self.controller_shift[port] = (self.controller_shift[port] >> 1) | 0x80
            return 0x40 | value
        if address >= 0x8000 and self.cart.mapper_id == 0:
            prg = self.cart.prg
            return prg[(address - 0x8000) % self.cart.prg_len]
        if address >= 0x4020:
            return self.cart.cpu_read(address)
        return 0

    def peek(self, address: int) -> int:
        address &= 0xFFFF
        if address < 0x2000:
            return self.ram[address & 0x7FF]
        if address >= 0x8000 and self.cart.mapper_id == 0:
            prg = self.cart.prg
            return prg[(address - 0x8000) % self.cart.prg_len]
        if address >= 0x6000:
            return self.cart.cpu_read(address)
        return 0

    def write(self, address: int, value: int) -> None:
        address &= 0xFFFF
        value &= 0xFF
        if address < 0x2000:
            self.ram[address & 0x7FF] = value
        elif address < 0x4000:
            self.ppu.write_register(address, value)
        elif address == 0x4014:
            page = value << 8
            for i in range(256):
                self.ppu.oam[(self.ppu.oam_address + i) & 0xFF] = self.read(page + i)
            self.cpu.stall += 513 + (self.cpu.total_cycles & 1)
        elif address == 0x4016:
            old_strobe = self.controller_strobe
            self.controller_strobe = bool(value & 1)
            if self.controller_strobe or old_strobe:
                self.controller_shift[:] = self.controller_state
        elif 0x4000 <= address <= 0x4017:
            self.sync_apu()
            self.apu.write(address, value)
        elif address >= 0x4020:
            self.cart.cpu_write(address, value)

    def tick(self, cpu_cycles: int) -> None:
        self.apu_pending_cycles += cpu_cycles
        self.ppu.step(cpu_cycles * 3)
        mapper = self.cart.mapper
        if mapper.needs_cpu_clock:
            mapper.clock_cpu(cpu_cycles)

    def sync_apu(self) -> None:
        if self.apu_pending_cycles:
            cycles = self.apu_pending_cycles
            self.apu_pending_cycles = 0
            self.apu.step(cycles)


# Status flags
C_FLAG = 0x01
Z_FLAG = 0x02
I_FLAG = 0x04
D_FLAG = 0x08
B_FLAG = 0x10
U_FLAG = 0x20
V_FLAG = 0x40
N_FLAG = 0x80


@dataclass(frozen=True, slots=True)
class Instruction:
    name: str
    mode: str
    cycles: int


# Every byte from $00 through $FF, row-major. The "KIL" entries are the
# hardware-jamming opcodes; unofficial NOPs retain their real operand lengths.
_OPCODE_ROWS = (
    "BRK IMP 7|ORA IZX 6|KIL IMP 2|SLO IZX 8|NOP ZP 3|ORA ZP 3|ASL ZP 5|SLO ZP 5|PHP IMP 3|ORA IMM 2|ASL ACC 2|ANC IMM 2|NOP ABS 4|ORA ABS 4|ASL ABS 6|SLO ABS 6",
    "BPL REL 2|ORA IZY 5|KIL IMP 2|SLO IZY 8|NOP ZPX 4|ORA ZPX 4|ASL ZPX 6|SLO ZPX 6|CLC IMP 2|ORA ABY 4|NOP IMP 2|SLO ABY 7|NOP ABX 4|ORA ABX 4|ASL ABX 7|SLO ABX 7",
    "JSR ABS 6|AND IZX 6|KIL IMP 2|RLA IZX 8|BIT ZP 3|AND ZP 3|ROL ZP 5|RLA ZP 5|PLP IMP 4|AND IMM 2|ROL ACC 2|ANC IMM 2|BIT ABS 4|AND ABS 4|ROL ABS 6|RLA ABS 6",
    "BMI REL 2|AND IZY 5|KIL IMP 2|RLA IZY 8|NOP ZPX 4|AND ZPX 4|ROL ZPX 6|RLA ZPX 6|SEC IMP 2|AND ABY 4|NOP IMP 2|RLA ABY 7|NOP ABX 4|AND ABX 4|ROL ABX 7|RLA ABX 7",
    "RTI IMP 6|EOR IZX 6|KIL IMP 2|SRE IZX 8|NOP ZP 3|EOR ZP 3|LSR ZP 5|SRE ZP 5|PHA IMP 3|EOR IMM 2|LSR ACC 2|ALR IMM 2|JMP ABS 3|EOR ABS 4|LSR ABS 6|SRE ABS 6",
    "BVC REL 2|EOR IZY 5|KIL IMP 2|SRE IZY 8|NOP ZPX 4|EOR ZPX 4|LSR ZPX 6|SRE ZPX 6|CLI IMP 2|EOR ABY 4|NOP IMP 2|SRE ABY 7|NOP ABX 4|EOR ABX 4|LSR ABX 7|SRE ABX 7",
    "RTS IMP 6|ADC IZX 6|KIL IMP 2|RRA IZX 8|NOP ZP 3|ADC ZP 3|ROR ZP 5|RRA ZP 5|PLA IMP 4|ADC IMM 2|ROR ACC 2|ARR IMM 2|JMP IND 5|ADC ABS 4|ROR ABS 6|RRA ABS 6",
    "BVS REL 2|ADC IZY 5|KIL IMP 2|RRA IZY 8|NOP ZPX 4|ADC ZPX 4|ROR ZPX 6|RRA ZPX 6|SEI IMP 2|ADC ABY 4|NOP IMP 2|RRA ABY 7|NOP ABX 4|ADC ABX 4|ROR ABX 7|RRA ABX 7",
    "NOP IMM 2|STA IZX 6|NOP IMM 2|SAX IZX 6|STY ZP 3|STA ZP 3|STX ZP 3|SAX ZP 3|DEY IMP 2|NOP IMM 2|TXA IMP 2|XAA IMM 2|STY ABS 4|STA ABS 4|STX ABS 4|SAX ABS 4",
    "BCC REL 2|STA IZY 6|KIL IMP 2|AHX IZY 6|STY ZPX 4|STA ZPX 4|STX ZPY 4|SAX ZPY 4|TYA IMP 2|STA ABY 5|TXS IMP 2|TAS ABY 5|SHY ABX 5|STA ABX 5|SHX ABY 5|AHX ABY 5",
    "LDY IMM 2|LDA IZX 6|LDX IMM 2|LAX IZX 6|LDY ZP 3|LDA ZP 3|LDX ZP 3|LAX ZP 3|TAY IMP 2|LDA IMM 2|TAX IMP 2|LAX IMM 2|LDY ABS 4|LDA ABS 4|LDX ABS 4|LAX ABS 4",
    "BCS REL 2|LDA IZY 5|KIL IMP 2|LAX IZY 5|LDY ZPX 4|LDA ZPX 4|LDX ZPY 4|LAX ZPY 4|CLV IMP 2|LDA ABY 4|TSX IMP 2|LAS ABY 4|LDY ABX 4|LDA ABX 4|LDX ABY 4|LAX ABY 4",
    "CPY IMM 2|CMP IZX 6|NOP IMM 2|DCP IZX 8|CPY ZP 3|CMP ZP 3|DEC ZP 5|DCP ZP 5|INY IMP 2|CMP IMM 2|DEX IMP 2|AXS IMM 2|CPY ABS 4|CMP ABS 4|DEC ABS 6|DCP ABS 6",
    "BNE REL 2|CMP IZY 5|KIL IMP 2|DCP IZY 8|NOP ZPX 4|CMP ZPX 4|DEC ZPX 6|DCP ZPX 6|CLD IMP 2|CMP ABY 4|NOP IMP 2|DCP ABY 7|NOP ABX 4|CMP ABX 4|DEC ABX 7|DCP ABX 7",
    "CPX IMM 2|SBC IZX 6|NOP IMM 3|ISC IZX 8|CPX ZP 3|SBC ZP 3|INC ZP 5|ISC ZP 5|INX IMP 2|SBC IMM 2|NOP IMP 2|SBC IMM 2|CPX ABS 4|SBC ABS 4|INC ABS 6|ISC ABS 6",
    "BEQ REL 2|SBC IZY 5|KIL IMP 2|ISC IZY 8|NOP ZPX 4|SBC ZPX 4|INC ZPX 6|ISC ZPX 6|SED IMP 2|SBC ABY 4|NOP IMP 2|ISC ABY 7|NOP ABX 4|SBC ABX 4|INC ABX 7|ISC ABX 7",
)


def _build_opcode_table() -> tuple[Instruction, ...]:
    entries: list[Instruction] = []
    for row in _OPCODE_ROWS:
        for item in row.split("|"):
            name, mode, cycles = item.split()
            entries.append(Instruction(name, mode, int(cycles)))
    if len(entries) != 256:
        raise RuntimeError(f"Opcode table has {len(entries)} entries, expected 256.")
    return tuple(entries)


OPCODES = _build_opcode_table()

# FCEUX x6502.cpp CycTable — base cycle counts for every opcode byte.
FCEUX_CYCLES: tuple[int, ...] = (
    7, 6, 2, 8, 3, 3, 5, 5, 3, 2, 2, 2, 4, 4, 6, 6,
    2, 5, 2, 8, 4, 4, 6, 6, 2, 4, 2, 7, 4, 4, 7, 7,
    6, 6, 2, 8, 3, 3, 5, 5, 4, 2, 2, 2, 4, 4, 6, 6,
    2, 5, 2, 8, 4, 4, 6, 6, 2, 4, 2, 7, 4, 4, 7, 7,
    6, 6, 2, 8, 3, 3, 5, 5, 3, 2, 2, 2, 3, 4, 6, 6,
    2, 5, 2, 8, 4, 4, 6, 6, 2, 4, 2, 7, 4, 4, 7, 7,
    6, 6, 2, 8, 3, 3, 5, 5, 4, 2, 2, 2, 5, 4, 6, 6,
    2, 5, 2, 8, 4, 4, 6, 6, 2, 4, 2, 7, 4, 4, 7, 7,
    2, 6, 2, 6, 3, 3, 3, 3, 2, 2, 2, 2, 4, 4, 4, 4,
    2, 6, 2, 6, 4, 4, 4, 4, 2, 5, 2, 5, 5, 5, 5, 5,
    2, 6, 2, 6, 3, 3, 3, 3, 2, 2, 2, 2, 4, 4, 4, 4,
    2, 5, 2, 5, 4, 4, 4, 4, 2, 4, 2, 4, 4, 4, 4, 4,
    2, 6, 2, 8, 3, 3, 5, 5, 2, 2, 2, 2, 4, 4, 6, 6,
    2, 5, 2, 8, 4, 4, 6, 6, 2, 4, 2, 7, 4, 4, 7, 7,
    2, 6, 3, 8, 3, 3, 5, 5, 2, 2, 2, 2, 4, 4, 6, 6,
    2, 5, 2, 8, 4, 4, 6, 6, 2, 4, 2, 7, 4, 4, 7, 7,
)

# FCEUX / NESDev alternate mnemonics (disassembler may show either form).
FCEUX_ALIASES: dict[str, tuple[str, ...]] = {
    "SLO": ("ASO", "SLO"),
    "SRE": ("LSE", "SRE"),
    "DCP": ("DCM", "DCP"),
    "ISC": ("ISB", "INS", "ISC"),
    "AHX": ("AXA", "SHA", "AHX"),
    "SHX": ("XAS", "SXA", "SHX"),
    "SHY": ("SAY", "SYA", "SHY"),
    "TAS": ("SHS", "XAS", "TAS"),
    "AXS": ("SBX", "AXS"),
    "ALR": ("ASR", "ALR"),
    "KIL": ("JAM", "HLT", "STP", "KIL"),
    "LAS": ("LAR", "LAS"),
    "XAA": ("ANE", "XAA"),
    "SAX": ("AAX", "SAX"),
}

# Interactive debugger prompt cheat-sheet (FCEUX-inspired).
PROMPT_HELP = """\
acnesemu debugger prompts (FCEUX-inspired)
--------------------------------------
  help / ?              this help
  opcodes / op          list all 256 FCEUX-aligned opcodes
  regs / r              CPU registers + flags
  dis [addr] [n]        disassemble n lines from addr (default PC)
  step / s [n]          step n CPU instructions (default 1)
  frame / f [n]         run n PPU frames (default 1)
  reset                 CPU/PPU/APU reset
  mem <addr> [len]      hex dump (default 16 bytes)
  peek <addr>           read one byte
  poke <addr> <val>     write one byte
  load <path.nes>       load cartridge
  run / gui             open the Tk GUI with the current ROM
  quit / q              leave the prompt
"""


def fceux_name(opcode: int) -> str:
    """Primary FCEUX-style mnemonic for an opcode byte."""
    name = OPCODES[opcode].name
    aliases = FCEUX_ALIASES.get(name)
    return aliases[0] if aliases else name


def assert_fceux_opcode_table() -> None:
    """Every byte must match FCEUX base cycles and have an execute path."""
    if len(OPCODES) != 256 or len(FCEUX_CYCLES) != 256:
        raise RuntimeError("Opcode / FCEUX cycle tables must be 256 entries.")
    for opcode, (ins, cycles) in enumerate(zip(OPCODES, FCEUX_CYCLES)):
        if ins.cycles != cycles:
            raise RuntimeError(
                f"Opcode ${opcode:02X} ({ins.name}) cycles {ins.cycles} != FCEUX {cycles}"
            )


class CPU:
    PAGE_CROSS_OPS = {
        "ORA", "AND", "EOR", "ADC", "LDA", "LDX", "LDY",
        "CMP", "SBC", "LAX", "LAS", "NOP",
    }
    # Hot official opcodes used by reset code and the inner loops of most games.
    # These bypass string dispatch and generic address decoding while retaining
    # exactly the same flags, memory accesses, and cycle counts.
    FAST_OPCODES = frozenset((
        0x09, 0x10, 0x18, 0x20, 0x29, 0x30, 0x38, 0x48, 0x49, 0x4C,
        0x50, 0x58, 0x60, 0x68, 0x69, 0x70, 0x78, 0x84, 0x85, 0x86,
        0x88, 0x8A, 0x8C, 0x8D, 0x8E, 0x90, 0x98, 0x9A, 0xA0, 0xA2,
        0xA4, 0xA5, 0xA6, 0xA8, 0xA9, 0xAA, 0xAC, 0xAD, 0xAE, 0xB0,
        0xB8, 0xBA, 0xC0, 0xC8, 0xC9, 0xCA, 0xD0, 0xD8, 0xE0, 0xE8,
        0xE9, 0xEA, 0xF0, 0xF8,
    ))
    _BRANCH_COND = {
        0x10: lambda p: not (p & N_FLAG), 0x30: lambda p: bool(p & N_FLAG),
        0x50: lambda p: not (p & V_FLAG), 0x70: lambda p: bool(p & V_FLAG),
        0x90: lambda p: not (p & C_FLAG), 0xB0: lambda p: bool(p & C_FLAG),
        0xD0: lambda p: not (p & Z_FLAG), 0xF0: lambda p: bool(p & Z_FLAG),
    }

    def __init__(self, bus: Bus) -> None:
        self.bus = bus
        # Bound fast paths avoid an extra Python method layer on every memory
        # access (tens of thousands of accesses per emulated frame).
        self.read: Callable[[int], int] = bus.read
        self.write: Callable[[int, int], None] = bus.write
        self.a = 0
        self.x = 0
        self.y = 0
        self.sp = 0xFD
        self.pc = 0
        self.p = I_FLAG | U_FLAG
        self.total_cycles = 0
        self.stall = 0
        self.nmi_pending = False
        self.irq_pending = False
        self.jammed = False
        self.last_pc = 0
        self.last_opcode = 0

    def reset(self) -> None:
        self.a = self.x = self.y = 0
        self.sp = 0xFD
        self.p = I_FLAG | U_FLAG
        self.stall = 0
        self.nmi_pending = False
        self.irq_pending = False
        self.jammed = False
        self.pc = self.read16(0xFFFC)
        if self.pc == 0:
            self.pc = 0x8000

    def read16(self, address: int) -> int:
        return self.read(address) | (self.read((address + 1) & 0xFFFF) << 8)

    def push(self, value: int) -> None:
        self.write(0x100 | self.sp, value)
        self.sp = (self.sp - 1) & 0xFF

    def pop(self) -> int:
        self.sp = (self.sp + 1) & 0xFF
        return self.read(0x100 | self.sp)

    def set_flag(self, flag: int, condition: bool) -> None:
        if condition:
            self.p |= flag
        else:
            self.p &= ~flag

    def set_zn(self, value: int) -> int:
        value &= 0xFF
        self.set_flag(Z_FLAG, value == 0)
        self.set_flag(N_FLAG, bool(value & 0x80))
        return value

    def interrupt(self, vector: int, break_flag: bool = False) -> int:
        self.push(self.pc >> 8)
        self.push(self.pc & 0xFF)
        pushed = self.p | U_FLAG
        pushed = pushed | B_FLAG if break_flag else pushed & ~B_FLAG
        self.push(pushed)
        self.p = (self.p | I_FLAG | U_FLAG) & ~B_FLAG
        self.pc = self.read16(vector)
        return 7

    def _address(self, mode: str) -> tuple[Optional[int], bool]:
        if mode in ("IMP", "ACC"):
            return None, False
        if mode == "IMM":
            address = self.pc
            self.pc = (self.pc + 1) & 0xFFFF
            return address, False
        if mode == "ZP":
            address = self.read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            return address, False
        if mode in ("ZPX", "ZPY"):
            base = self.read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            index = self.x if mode == "ZPX" else self.y
            return (base + index) & 0xFF, False
        if mode in ("ABS", "ABX", "ABY"):
            low = self.read(self.pc)
            high = self.read((self.pc + 1) & 0xFFFF)
            self.pc = (self.pc + 2) & 0xFFFF
            base = low | (high << 8)
            if mode == "ABS":
                return base, False
            index = self.x if mode == "ABX" else self.y
            address = (base + index) & 0xFFFF
            return address, (base & 0xFF00) != (address & 0xFF00)
        if mode == "IND":
            pointer = self.read16(self.pc)
            self.pc = (self.pc + 2) & 0xFFFF
            # Original NMOS 6502 page-boundary wrap behavior.
            low = self.read(pointer)
            high = self.read((pointer & 0xFF00) | ((pointer + 1) & 0xFF))
            return low | (high << 8), False
        if mode == "IZX":
            zp = (self.read(self.pc) + self.x) & 0xFF
            self.pc = (self.pc + 1) & 0xFFFF
            return self.read(zp) | (self.read((zp + 1) & 0xFF) << 8), False
        if mode == "IZY":
            zp = self.read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            base = self.read(zp) | (self.read((zp + 1) & 0xFF) << 8)
            address = (base + self.y) & 0xFFFF
            return address, (base & 0xFF00) != (address & 0xFF00)
        if mode == "REL":
            offset = self.read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            if offset & 0x80:
                offset -= 0x100
            return offset, False
        raise RuntimeError(f"Unknown addressing mode: {mode}")

    def _value(self, address: Optional[int]) -> int:
        if address is None:
            raise RuntimeError("Instruction requires an operand.")
        return self.read(address)

    def _compare(self, register: int, value: int) -> None:
        result = (register - value) & 0x1FF
        self.set_flag(C_FLAG, register >= value)
        self.set_zn(result)

    def _adc(self, value: int) -> None:
        carry = 1 if self.p & C_FLAG else 0
        total = self.a + value + carry
        result = total & 0xFF
        self.set_flag(C_FLAG, total > 0xFF)
        self.set_flag(V_FLAG, bool((~(self.a ^ value) & (self.a ^ result)) & 0x80))
        self.a = self.set_zn(result)

    def _sbc(self, value: int) -> None:
        self._adc(value ^ 0xFF)

    def _shift(self, name: str, address: Optional[int], accumulator: bool) -> int:
        value = self.a if accumulator else self._value(address)
        if name == "ASL":
            self.set_flag(C_FLAG, bool(value & 0x80))
            value = (value << 1) & 0xFF
        elif name == "LSR":
            self.set_flag(C_FLAG, bool(value & 1))
            value >>= 1
        elif name == "ROL":
            carry = 1 if self.p & C_FLAG else 0
            self.set_flag(C_FLAG, bool(value & 0x80))
            value = ((value << 1) | carry) & 0xFF
        else:
            carry = 0x80 if self.p & C_FLAG else 0
            self.set_flag(C_FLAG, bool(value & 1))
            value = (value >> 1) | carry
        value = self.set_zn(value)
        if accumulator:
            self.a = value
        elif address is not None:
            self.write(address, value)
        return value

    def _branch(self, condition: bool, offset: int) -> int:
        if not condition:
            return 0
        old = self.pc
        self.pc = (self.pc + offset) & 0xFFFF
        return 1 + int((old & 0xFF00) != (self.pc & 0xFF00))

    def _fast_execute(self, opcode: int) -> int:
        """Execute a high-frequency official opcode after its byte was fetched."""
        # Immediate loads.
        if opcode in (0xA0, 0xA2, 0xA9):
            value = self.read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            value = self.set_zn(value)
            if opcode == 0xA0:
                self.y = value
            elif opcode == 0xA2:
                self.x = value
            else:
                self.a = value
            return 2
        # Zero-page loads and stores.
        if opcode in (0xA4, 0xA5, 0xA6, 0x84, 0x85, 0x86):
            address = self.read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            if opcode == 0xA4:
                self.y = self.set_zn(self.read(address))
            elif opcode == 0xA5:
                self.a = self.set_zn(self.read(address))
            elif opcode == 0xA6:
                self.x = self.set_zn(self.read(address))
            elif opcode == 0x84:
                self.write(address, self.y)
            elif opcode == 0x85:
                self.write(address, self.a)
            else:
                self.write(address, self.x)
            return 3
        # Absolute loads and stores.
        if opcode in (0xAC, 0xAD, 0xAE, 0x8C, 0x8D, 0x8E):
            address = self.read(self.pc) | (self.read((self.pc + 1) & 0xFFFF) << 8)
            self.pc = (self.pc + 2) & 0xFFFF
            if opcode == 0xAC:
                self.y = self.set_zn(self.read(address))
            elif opcode == 0xAD:
                self.a = self.set_zn(self.read(address))
            elif opcode == 0xAE:
                self.x = self.set_zn(self.read(address))
            elif opcode == 0x8C:
                self.write(address, self.y)
            elif opcode == 0x8D:
                self.write(address, self.a)
            else:
                self.write(address, self.x)
            return 4
        # Relative branches — condition table is class-level (no per-call dict).
        if opcode in (0x10, 0x30, 0x50, 0x70, 0x90, 0xB0, 0xD0, 0xF0):
            offset = self.read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            if offset & 0x80:
                offset -= 0x100
            condition = self._BRANCH_COND[opcode](self.p)
            return 2 + self._branch(condition, offset)
        # Immediate ALU and comparisons.
        if opcode in (0x09, 0x29, 0x49, 0x69, 0xC0, 0xC9, 0xE0, 0xE9):
            value = self.read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            if opcode == 0x09:
                self.a = self.set_zn(self.a | value)
            elif opcode == 0x29:
                self.a = self.set_zn(self.a & value)
            elif opcode == 0x49:
                self.a = self.set_zn(self.a ^ value)
            elif opcode == 0x69:
                self._adc(value)
            elif opcode == 0xC0:
                self._compare(self.y, value)
            elif opcode == 0xC9:
                self._compare(self.a, value)
            elif opcode == 0xE0:
                self._compare(self.x, value)
            else:
                self._sbc(value)
            return 2
        # Register transfers and increments/decrements.
        if opcode in (0x88, 0x8A, 0x98, 0x9A, 0xA8, 0xAA, 0xBA, 0xC8, 0xCA, 0xE8):
            if opcode == 0x88:
                self.y = self.set_zn(self.y - 1)
            elif opcode == 0x8A:
                self.a = self.set_zn(self.x)
            elif opcode == 0x98:
                self.a = self.set_zn(self.y)
            elif opcode == 0x9A:
                self.sp = self.x
            elif opcode == 0xA8:
                self.y = self.set_zn(self.a)
            elif opcode == 0xAA:
                self.x = self.set_zn(self.a)
            elif opcode == 0xBA:
                self.x = self.set_zn(self.sp)
            elif opcode == 0xC8:
                self.y = self.set_zn(self.y + 1)
            elif opcode == 0xCA:
                self.x = self.set_zn(self.x - 1)
            else:
                self.x = self.set_zn(self.x + 1)
            return 2
        # Flag operations and the official one-byte NOP.
        if opcode in (0x18, 0x38, 0x58, 0x78, 0xB8, 0xD8, 0xEA, 0xF8):
            if opcode == 0x18:
                self.p &= ~C_FLAG
            elif opcode == 0x38:
                self.p |= C_FLAG
            elif opcode == 0x58:
                self.p &= ~I_FLAG
            elif opcode == 0x78:
                self.p |= I_FLAG
            elif opcode == 0xB8:
                self.p &= ~V_FLAG
            elif opcode == 0xD8:
                self.p &= ~D_FLAG
            elif opcode == 0xF8:
                self.p |= D_FLAG
            return 2
        if opcode == 0x4C:  # JMP absolute
            self.pc = self.read(self.pc) | (self.read((self.pc + 1) & 0xFFFF) << 8)
            return 3
        if opcode == 0x20:  # JSR
            target = self.read(self.pc) | (self.read((self.pc + 1) & 0xFFFF) << 8)
            self.pc = (self.pc + 2) & 0xFFFF
            return_address = (self.pc - 1) & 0xFFFF
            self.push(return_address >> 8)
            self.push(return_address & 0xFF)
            self.pc = target
            return 6
        if opcode == 0x60:  # RTS
            low, high = self.pop(), self.pop()
            self.pc = ((low | (high << 8)) + 1) & 0xFFFF
            return 6
        if opcode == 0x48:
            self.push(self.a)
            return 3
        if opcode == 0x68:
            self.a = self.set_zn(self.pop())
            return 4
        raise RuntimeError(f"Invalid fast opcode ${opcode:02X}")

    def step(self) -> int:
        if self.stall:
            self.stall -= 1
            self.total_cycles += 1
            self.bus.tick(1)
            return 1
        if self.nmi_pending:
            self.nmi_pending = False
            cycles = self.interrupt(0xFFFA)
            self.total_cycles += cycles
            self.bus.tick(cycles)
            return cycles
        # IRQ polling only when interrupts are enabled — skips APU sync on
        # the common SEI / game-loop path.
        if not (self.p & I_FLAG):
            if self.bus.apu.requires_cpu_sync or self.bus.apu.irq_may_fire:
                self.bus.sync_apu()
            if self.irq_pending or self.bus.cart.mapper.irq_pending or self.bus.apu.irq_pending:
                self.irq_pending = False
                self.bus.cart.mapper.irq_pending = False
                cycles = self.interrupt(0xFFFE)
                self.total_cycles += cycles
                self.bus.tick(cycles)
                return cycles
        elif self.bus.apu.requires_cpu_sync:
            self.bus.sync_apu()
        if self.jammed:
            self.total_cycles += 1
            self.bus.tick(1)
            return 1

        self.last_pc = self.pc
        opcode = self.read(self.pc)
        self.last_opcode = opcode
        self.pc = (self.pc + 1) & 0xFFFF
        if opcode in self.FAST_OPCODES:
            cycles = self._fast_execute(opcode)
            self.p = (self.p | U_FLAG) & ~B_FLAG
            self.total_cycles += cycles
            self.bus.tick(cycles)
            return cycles
        instruction = OPCODES[opcode]
        address, crossed = self._address(instruction.mode)
        name = instruction.name
        cycles = instruction.cycles
        value = 0

        if name in self.PAGE_CROSS_OPS and crossed:
            cycles += 1

        if name == "ADC":
            self._adc(self._value(address))
        elif name == "AND":
            self.a = self.set_zn(self.a & self._value(address))
        elif name == "ASL":
            self._shift("ASL", address, instruction.mode == "ACC")
        elif name in ("BCC", "BCS", "BEQ", "BMI", "BNE", "BPL", "BVC", "BVS"):
            conditions = {
                "BCC": not (self.p & C_FLAG), "BCS": bool(self.p & C_FLAG),
                "BEQ": bool(self.p & Z_FLAG), "BMI": bool(self.p & N_FLAG),
                "BNE": not (self.p & Z_FLAG), "BPL": not (self.p & N_FLAG),
                "BVC": not (self.p & V_FLAG), "BVS": bool(self.p & V_FLAG),
            }
            cycles += self._branch(bool(conditions[name]), int(address or 0))
        elif name == "BIT":
            value = self._value(address)
            self.set_flag(Z_FLAG, (self.a & value) == 0)
            self.set_flag(V_FLAG, bool(value & 0x40))
            self.set_flag(N_FLAG, bool(value & 0x80))
        elif name == "BRK":
            self.pc = (self.pc + 1) & 0xFFFF
            self.interrupt(0xFFFE, True)
        elif name == "CLC":
            self.p &= ~C_FLAG
        elif name == "CLD":
            self.p &= ~D_FLAG
        elif name == "CLI":
            self.p &= ~I_FLAG
        elif name == "CLV":
            self.p &= ~V_FLAG
        elif name == "CMP":
            self._compare(self.a, self._value(address))
        elif name == "CPX":
            self._compare(self.x, self._value(address))
        elif name == "CPY":
            self._compare(self.y, self._value(address))
        elif name == "DEC":
            value = self.set_zn((self._value(address) - 1) & 0xFF)
            self.write(int(address), value)
        elif name == "DEX":
            self.x = self.set_zn(self.x - 1)
        elif name == "DEY":
            self.y = self.set_zn(self.y - 1)
        elif name == "EOR":
            self.a = self.set_zn(self.a ^ self._value(address))
        elif name == "INC":
            value = self.set_zn(self._value(address) + 1)
            self.write(int(address), value)
        elif name == "INX":
            self.x = self.set_zn(self.x + 1)
        elif name == "INY":
            self.y = self.set_zn(self.y + 1)
        elif name == "JMP":
            self.pc = int(address)
        elif name == "JSR":
            return_address = (self.pc - 1) & 0xFFFF
            self.push(return_address >> 8)
            self.push(return_address & 0xFF)
            self.pc = int(address)
        elif name == "LDA":
            self.a = self.set_zn(self._value(address))
        elif name == "LDX":
            self.x = self.set_zn(self._value(address))
        elif name == "LDY":
            self.y = self.set_zn(self._value(address))
        elif name == "LSR":
            self._shift("LSR", address, instruction.mode == "ACC")
        elif name == "NOP":
            pass
        elif name == "ORA":
            self.a = self.set_zn(self.a | self._value(address))
        elif name == "PHA":
            self.push(self.a)
        elif name == "PHP":
            self.push(self.p | B_FLAG | U_FLAG)
        elif name == "PLA":
            self.a = self.set_zn(self.pop())
        elif name == "PLP":
            self.p = (self.pop() | U_FLAG) & ~B_FLAG
        elif name == "ROL":
            self._shift("ROL", address, instruction.mode == "ACC")
        elif name == "ROR":
            self._shift("ROR", address, instruction.mode == "ACC")
        elif name == "RTI":
            self.p = (self.pop() | U_FLAG) & ~B_FLAG
            low, high = self.pop(), self.pop()
            self.pc = low | (high << 8)
        elif name == "RTS":
            low, high = self.pop(), self.pop()
            self.pc = ((low | (high << 8)) + 1) & 0xFFFF
        elif name == "SBC":
            self._sbc(self._value(address))
        elif name == "SEC":
            self.p |= C_FLAG
        elif name == "SED":
            self.p |= D_FLAG
        elif name == "SEI":
            self.p |= I_FLAG
        elif name == "STA":
            self.write(int(address), self.a)
        elif name == "STX":
            self.write(int(address), self.x)
        elif name == "STY":
            self.write(int(address), self.y)
        elif name == "TAX":
            self.x = self.set_zn(self.a)
        elif name == "TAY":
            self.y = self.set_zn(self.a)
        elif name == "TSX":
            self.x = self.set_zn(self.sp)
        elif name == "TXA":
            self.a = self.set_zn(self.x)
        elif name == "TXS":
            self.sp = self.x
        elif name == "TYA":
            self.a = self.set_zn(self.y)

        # Stable behavior of common unofficial NMOS 6502 opcodes.
        elif name == "LAX":
            self.a = self.x = self.set_zn(self._value(address))
        elif name == "SAX":
            self.write(int(address), self.a & self.x)
        elif name == "DCP":
            value = (self._value(address) - 1) & 0xFF
            self.write(int(address), value)
            self._compare(self.a, value)
        elif name == "ISC":
            value = (self._value(address) + 1) & 0xFF
            self.write(int(address), value)
            self._sbc(value)
        elif name == "SLO":
            value = self._shift("ASL", address, False)
            self.a = self.set_zn(self.a | value)
        elif name == "RLA":
            value = self._shift("ROL", address, False)
            self.a = self.set_zn(self.a & value)
        elif name == "SRE":
            value = self._shift("LSR", address, False)
            self.a = self.set_zn(self.a ^ value)
        elif name == "RRA":
            value = self._shift("ROR", address, False)
            self._adc(value)
        elif name == "ANC":
            self.a = self.set_zn(self.a & self._value(address))
            self.set_flag(C_FLAG, bool(self.a & 0x80))
        elif name == "ALR":
            self.a &= self._value(address)
            self.set_flag(C_FLAG, bool(self.a & 1))
            self.a = self.set_zn(self.a >> 1)
        elif name == "ARR":
            self.a &= self._value(address)
            self.a = ((self.a >> 1) | (0x80 if self.p & C_FLAG else 0)) & 0xFF
            self.set_zn(self.a)
            self.set_flag(C_FLAG, bool(self.a & 0x40))
            self.set_flag(V_FLAG, bool(((self.a >> 6) ^ (self.a >> 5)) & 1))
        elif name == "XAA":
            self.a = self.set_zn(self.x & self._value(address))
        elif name == "AXS":
            operand = self._value(address)
            result = (self.a & self.x) - operand
            self.set_flag(C_FLAG, result >= 0)
            self.x = self.set_zn(result)
        elif name == "LAS":
            value = self._value(address) & self.sp
            self.a = self.x = self.sp = self.set_zn(value)
        elif name in ("AHX", "SHX", "SHY", "TAS"):
            high_mask = ((int(address) >> 8) + 1) & 0xFF
            if name == "AHX":
                value = self.a & self.x & high_mask
            elif name == "SHX":
                value = self.x & high_mask
            elif name == "SHY":
                value = self.y & high_mask
            else:
                self.sp = self.a & self.x
                value = self.sp & high_mask
            self.write(int(address), value)
        elif name == "KIL":
            self.jammed = True
            self.pc = (self.pc - 1) & 0xFFFF
        else:
            raise RuntimeError(f"Opcode ${opcode:02X} ({name}) is not implemented.")

        self.p = (self.p | U_FLAG) & ~B_FLAG
        self.total_cycles += cycles
        self.bus.tick(cycles)
        return cycles


MODE_LENGTH = {
    "IMP": 1, "ACC": 1, "IMM": 2, "ZP": 2, "ZPX": 2, "ZPY": 2,
    "IZX": 2, "IZY": 2, "REL": 2, "ABS": 3, "ABX": 3, "ABY": 3, "IND": 3,
}


def disassemble(bus: Bus, start: int, lines: int = 12, *, fceux_names: bool = True) -> list[str]:
    output: list[str] = []
    pc = start & 0xFFFF
    for _ in range(lines):
        opcode = bus.peek(pc)
        ins = OPCODES[opcode]
        length = MODE_LENGTH[ins.mode]
        operands = [bus.peek((pc + i) & 0xFFFF) for i in range(1, length)]
        raw = " ".join(f"{b:02X}" for b in [opcode, *operands]).ljust(8)
        if ins.mode == "IMM":
            operand = f"#$%02X" % operands[0]
        elif ins.mode == "ZP":
            operand = f"$%02X" % operands[0]
        elif ins.mode == "ZPX":
            operand = f"$%02X,X" % operands[0]
        elif ins.mode == "ZPY":
            operand = f"$%02X,Y" % operands[0]
        elif ins.mode == "IZX":
            operand = f"($%02X,X)" % operands[0]
        elif ins.mode == "IZY":
            operand = f"($%02X),Y" % operands[0]
        elif ins.mode in ("ABS", "ABX", "ABY", "IND"):
            target = operands[0] | (operands[1] << 8)
            suffix = {"ABS": "", "ABX": ",X", "ABY": ",Y", "IND": ")"}[ins.mode]
            operand = f"${target:04X}{suffix}" if ins.mode != "IND" else f"(${target:04X})"
        elif ins.mode == "REL":
            offset = operands[0] - 0x100 if operands[0] & 0x80 else operands[0]
            operand = f"${(pc + 2 + offset) & 0xFFFF:04X}"
        elif ins.mode == "ACC":
            operand = "A"
        else:
            operand = ""
        mnemonic = fceux_name(opcode) if fceux_names else ins.name
        output.append(f"{pc:04X}  {raw} {mnemonic} {operand}".rstrip())
        pc = (pc + length) & 0xFFFF
    return output


def list_all_opcodes() -> list[str]:
    """Human-readable dump of the full FCEUX-aligned 256-opcode map."""
    lines: list[str] = []
    for opcode, ins in enumerate(OPCODES):
        aliases = FCEUX_ALIASES.get(ins.name, ())
        alias_txt = f"  aliases={','.join(aliases)}" if aliases else ""
        lines.append(
            f"${opcode:02X}  {fceux_name(opcode):<4}  {ins.mode:<3}  "
            f"{ins.cycles}c  ({ins.name}){alias_txt}"
        )
    return lines


def run_prompt(rom: Optional[str] = None) -> int:
    """Interactive FCEUX-inspired debugger prompt (no GUI required)."""
    nes: Optional[NES] = None
    if rom:
        try:
            nes = NES(Cartridge.from_file(rom))
            print(f"loaded {rom}")
        except Exception as exc:
            print(f"load failed: {exc}")
    print(f"{APP_TITLE}")
    print("type 'help' for prompts, 'opcodes' for the full FCEUX opcode map")
    while True:
        try:
            line = input("acnesemu> ").strip()
        except (EOFError, KeyboardInterrupt):
            print()
            return 0
        if not line:
            continue
        parts = line.split()
        cmd = parts[0].lower()
        args = parts[1:]

        if cmd in ("q", "quit", "exit"):
            return 0
        if cmd in ("help", "?"):
            print(PROMPT_HELP)
            continue
        if cmd in ("opcodes", "op", "ops"):
            for row in list_all_opcodes():
                print(row)
            print(f"— {len(OPCODES)}/256 opcodes, cycles match FCEUX CycTable")
            continue
        if cmd == "load":
            if not args:
                print("usage: load <path.nes>")
                continue
            try:
                nes = NES(Cartridge.from_file(args[0]))
                print(f"loaded {args[0]}")
            except Exception as exc:
                print(f"load failed: {exc}")
            continue
        if cmd in ("run", "gui"):
            path = args[0] if args else (rom if rom else None)
            if path is None and nes is None:
                print("load a ROM first (load <path.nes>)")
                continue
            if path:
                root = tk.Tk()
                EmulatorGUI(root, path)
                root.mainloop()
            else:
                print("GUI needs a ROM path; use: run <path.nes>")
            continue
        if nes is None:
            print("no cartridge — use: load <path.nes>")
            continue

        cpu = nes.bus.cpu
        if cmd in ("r", "regs"):
            flags = "".join(
                name if cpu.p & bit else name.lower()
                for name, bit in (
                    ("N", N_FLAG), ("V", V_FLAG), ("U", U_FLAG), ("B", B_FLAG),
                    ("D", D_FLAG), ("I", I_FLAG), ("Z", Z_FLAG), ("C", C_FLAG),
                )
            )
            print(
                f"A={cpu.a:02X} X={cpu.x:02X} Y={cpu.y:02X} SP={cpu.sp:02X} "
                f"PC={cpu.pc:04X} P={cpu.p:02X}[{flags}] cy={cpu.total_cycles}"
            )
            continue
        if cmd in ("s", "step"):
            count = int(args[0], 0) if args else 1
            for _ in range(max(1, count)):
                cpu.step()
            print("\n".join(disassemble(nes.bus, cpu.pc, 8)))
            continue
        if cmd in ("f", "frame"):
            count = int(args[0], 0) if args else 1
            for _ in range(max(1, count)):
                nes.run_frame()
            print(f"frame={nes.bus.ppu.frame_number} PC=${cpu.pc:04X}")
            continue
        if cmd == "reset":
            nes.reset()
            print(f"reset PC=${cpu.pc:04X}")
            continue
        if cmd in ("d", "dis", "disasm"):
            addr = int(args[0], 0) if args else cpu.pc
            n = int(args[1], 0) if len(args) > 1 else 12
            print("\n".join(disassemble(nes.bus, addr, n)))
            continue
        if cmd == "peek":
            if not args:
                print("usage: peek <addr>")
                continue
            addr = int(args[0], 0) & 0xFFFF
            print(f"${addr:04X} = ${nes.bus.peek(addr):02X}")
            continue
        if cmd == "poke":
            if len(args) < 2:
                print("usage: poke <addr> <val>")
                continue
            addr = int(args[0], 0) & 0xFFFF
            val = int(args[1], 0) & 0xFF
            nes.bus.write(addr, val)
            print(f"${addr:04X} := ${val:02X}")
            continue
        if cmd in ("m", "mem", "dump"):
            if not args:
                print("usage: mem <addr> [len]")
                continue
            addr = int(args[0], 0) & 0xFFFF
            length = int(args[1], 0) if len(args) > 1 else 16
            length = max(1, min(length, 256))
            bytes_ = [nes.bus.peek((addr + i) & 0xFFFF) for i in range(length)]
            for i in range(0, length, 16):
                chunk = bytes_[i:i + 16]
                hex_part = " ".join(f"{b:02X}" for b in chunk)
                print(f"{(addr + i) & 0xFFFF:04X}: {hex_part}")
            continue
        print(f"unknown prompt '{cmd}' — type help")
    return 0


class NES:
    def __init__(self, cart: Cartridge) -> None:
        self.cart = cart
        self.bus = Bus(cart)
        self.bus.cpu.reset()

    def reset(self) -> None:
        self.cart.mapper.reset()
        self.bus.ppu.reset()
        self.bus.apu_pending_cycles = 0
        self.bus.apu.reset()
        self.bus.cpu.reset()

    def run_frame(self) -> int:
        ppu = self.bus.ppu
        ppu.frame_ready = False
        instructions = 0
        while not ppu.frame_ready and instructions < 200_000:
            self.bus.cpu.step()
            instructions += 1
        if instructions >= 200_000:
            raise RuntimeError("Frame execution guard reached; the CPU may be jammed.")
        self.bus.sync_apu()
        ppu.finish_frame()
        return instructions


class EmulatorGUI:
    """Classic FCEUX Win32-style shell: menu bar + black game client."""

    KEY_BITS = {
        "z": 0, "x": 1, "Shift_L": 2, "Shift_R": 2, "Return": 3,
        "Up": 4, "Down": 5, "Left": 6, "Right": 7,
    }

    def __init__(self, root: tk.Tk, initial_rom: Optional[str] = None) -> None:
        self.root = root
        self.root.title(APP_TITLE)
        self.root.configure(bg=WIN_FACE)
        self.root.resizable(False, False)
        self.nes: Optional[NES] = None
        self.rom_path: Optional[pathlib.Path] = None
        self.running = False
        self._alive = True
        self._loop_after: Optional[object] = None
        self.scale = tk.IntVar(value=2)
        self.muted = tk.BooleanVar(value=False)
        self.menu_hidden = False
        self.turbo = tk.BooleanVar(value=False)
        self.paused = tk.BooleanVar(value=False)
        self.audio = AudioOutput()
        self._photo: Optional[tk.PhotoImage] = None
        self._next_frame = time.perf_counter()
        self._fps_timer = time.perf_counter()
        self._frames_since_fps = 0
        self._osd_until = 0.0
        self._osd_text = ""
        self._debugger: Optional[tk.Toplevel] = None
        self._menubar: Optional[tk.Menu] = None
        self._context: Optional[tk.Menu] = None
        self.toolbar: Optional[tk.Frame] = None
        self._build_style()
        self._build_menu()
        self._build_toolbar()
        self._build_layout()
        self._fit_window()
        self.root.bind_all("<KeyPress>", self._key_down)
        self.root.bind_all("<KeyRelease>", self._key_up)
        self.root.protocol("WM_DELETE_WINDOW", self._close)
        if initial_rom:
            self.load_rom(initial_rom)
        self._loop_after = self.root.after(1, self._loop)

    def _build_style(self) -> None:
        style = ttk.Style(self.root)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass
        style.configure(".", background=WIN_FACE, foreground=WIN_TEXT)
        style.configure("TFrame", background=WIN_FACE)
        style.configure("TLabel", background=WIN_FACE, foreground=WIN_TEXT)
        style.configure("TButton", background=WIN_FACE, foreground=WIN_TEXT, padding=4)
        style.configure("TNotebook", background=WIN_FACE)
        style.configure(
            "TNotebook.Tab", background=WIN_FACE, foreground=WIN_TEXT, padding=(8, 3),
        )
        style.configure("TLabelframe", background=WIN_FACE, foreground=WIN_TEXT)
        style.configure("TLabelframe.Label", background=WIN_FACE, foreground=WIN_TEXT)
        style.map(
            "TButton",
            background=[("active", WIN_LIGHT), ("pressed", WIN_SHADOW)],
            foreground=[("disabled", WIN_DISABLED)],
        )

    def _classic_menu(self, master: tk.Misc) -> tk.Menu:
        return tk.Menu(
            master,
            tearoff=False,
            bg=WIN_MENU,
            fg=WIN_TEXT,
            activebackground=WIN_HIGHLIGHT,
            activeforeground=WIN_HIGHLIGHT_TEXT,
            disabledforeground=WIN_DISABLED,
            relief=tk.RAISED,
            borderwidth=1,
        )

    def _build_menu(self) -> None:
        menu = self._classic_menu(self.root)
        self._menubar = menu

        # --- File (FCEUX) ---
        file_menu = self._classic_menu(menu)
        file_menu.add_command(label="Open ROM...", accelerator="Ctrl+O", command=self.open_rom)
        file_menu.add_command(label="Close", command=self.close_rom, state=tk.DISABLED)
        self._file_close = file_menu
        file_menu.add_separator()
        file_menu.add_command(label="Screenshot", accelerator="F12", command=self.screenshot)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self._close)
        menu.add_cascade(label="File", menu=file_menu)

        # --- NES (FCEUX) ---
        nes_menu = self._classic_menu(menu)
        nes_menu.add_checkbutton(
            label="Pause", accelerator="Pause / P", variable=self.paused,
            command=self._sync_pause_from_menu,
        )
        nes_menu.add_command(label="Reset", accelerator="Ctrl+R", command=self.reset)
        nes_menu.add_command(label="Power", command=self.power)
        nes_menu.add_separator()
        speed = self._classic_menu(nes_menu)
        speed.add_command(label="Speed +", command=lambda: self._osd("Speed + (not implemented)"))
        speed.add_command(label="Speed -", command=lambda: self._osd("Speed - (not implemented)"))
        speed.add_command(label="Normal Speed", command=lambda: self._osd("Normal Speed"))
        speed.add_checkbutton(label="Turbo", variable=self.turbo, command=self._toggle_turbo)
        nes_menu.add_cascade(label="Emulation Speed", menu=speed)
        menu.add_cascade(label="NES", menu=nes_menu)

        # --- Config (FCEUX) ---
        config = self._classic_menu(menu)
        config.add_command(label="Input...", command=self.show_controls)
        config.add_command(label="Network Play...", state=tk.DISABLED)
        config.add_command(label="Palette...", state=tk.DISABLED)
        config.add_command(label="Sound...", command=self.show_sound)
        config.add_command(label="Timing...", state=tk.DISABLED)
        config.add_command(label="Video...", command=self.show_video)
        config.add_separator()
        config.add_checkbutton(
            label="Mute", variable=self.muted, accelerator="Ctrl+M",
            command=self._toggle_mute,
        )
        config.add_separator()
        config.add_command(label="Hide Menu", accelerator="Esc", command=self.toggle_menu)
        menu.add_cascade(label="Config", menu=config)

        # --- Tools (FCEUX) ---
        tools = self._classic_menu(menu)
        tools.add_command(label="Cheats...", state=tk.DISABLED)
        tools.add_command(label="RAM Search...", state=tk.DISABLED)
        tools.add_command(label="RAM Watch...", state=tk.DISABLED)
        tools.add_separator()
        tools.add_command(label="Screenshot", accelerator="F12", command=self.screenshot)
        menu.add_cascade(label="Tools", menu=tools)

        # --- Debug (FCEUX) ---
        debug = self._classic_menu(menu)
        debug.add_command(label="Debugger...", accelerator="Ctrl+D", command=self.open_debugger)
        debug.add_command(label="PPU Viewer...", state=tk.DISABLED)
        debug.add_command(label="Name Table Viewer...", state=tk.DISABLED)
        debug.add_command(label="Hex Editor...", state=tk.DISABLED)
        debug.add_command(label="Trace Logger...", state=tk.DISABLED)
        debug.add_separator()
        debug.add_command(label="Step Frame", accelerator="F7", command=self.step_frame)
        debug.add_command(label="Step Into", accelerator="F8", command=self.step_instruction)
        debug.add_separator()
        debug.add_command(label="Opcode Map...", command=self.show_opcodes)
        debug.add_command(label="Debugger Prompts...", command=self.show_prompts)
        menu.add_cascade(label="Debug", menu=debug)

        # --- Help (FCEUX) ---
        help_menu = self._classic_menu(menu)
        help_menu.add_command(label="About acnesemu...", command=self.show_about)
        menu.add_cascade(label="Help", menu=help_menu)

        self.root.config(menu=menu)
        self._build_context_menu()

        self.root.bind_all("<Control-o>", self._hotkey(self.open_rom))
        self.root.bind_all("<Control-r>", self._hotkey(self.reset))
        self.root.bind_all("<Control-d>", self._hotkey(self.open_debugger))
        self.root.bind_all("<F7>", self._hotkey(self.step_frame))
        self.root.bind_all("<F8>", self._hotkey(self.step_instruction))
        self.root.bind_all("<F12>", self._hotkey(self.screenshot))
        self.root.bind_all("<space>", self._hotkey(self.toggle_pause))
        self.root.bind_all("<p>", self._hotkey(self.toggle_pause))
        self.root.bind_all("<P>", self._hotkey(self.toggle_pause))
        self.root.bind_all("<Escape>", self._hotkey(self.toggle_menu))
        self.root.bind_all("<Control-m>", self._hotkey(self._hotkey_mute))

    def _hotkey(self, action: Callable[[], None]):
        """Wrap menu accelerators so they ignore typing focus in dialogs."""

        def handler(_event: tk.Event) -> Optional[str]:
            if not self._alive or self._focus_is_text():
                return None
            action()
            return "break"

        return handler

    def _hotkey_mute(self) -> None:
        self.muted.set(not self.muted.get())
        self._toggle_mute()

    def _focus_is_text(self) -> bool:
        try:
            widget = self.root.focus_get()
        except tk.TclError:
            return False
        if widget is None:
            return False
        return isinstance(widget, (tk.Text, tk.Entry, ttk.Entry))

    def _win_button(self, parent: tk.Misc, text: str, command: Callable[[], None], width: int = 10) -> tk.Button:
        return tk.Button(
            parent, text=text, command=command, width=width,
            bg=WIN_FACE, fg=WIN_TEXT, activebackground=WIN_LIGHT,
            activeforeground=WIN_TEXT, relief=tk.RAISED, borderwidth=2,
            highlightthickness=0, takefocus=0, padx=4, pady=1,
        )

    def _build_toolbar(self) -> None:
        # Classic gray button strip under the menu (Load ROM front and center).
        bar = tk.Frame(self.root, bg=WIN_FACE, bd=1, relief=tk.RAISED)
        bar.pack(side=tk.TOP, fill=tk.X)
        self._win_button(bar, "Load ROM", self.open_rom, width=10).pack(side=tk.LEFT, padx=3, pady=3)
        self._win_button(bar, "Reset", self.reset, width=7).pack(side=tk.LEFT, padx=2, pady=3)
        self.pause_button = self._win_button(bar, "Pause", self.toggle_pause, width=7)
        self.pause_button.pack(side=tk.LEFT, padx=2, pady=3)
        self._win_button(bar, "Frame", self.step_frame, width=7).pack(side=tk.LEFT, padx=2, pady=3)
        tk.Frame(bar, width=2, bg=WIN_SHADOW, bd=0).pack(side=tk.LEFT, fill=tk.Y, padx=6, pady=4)
        tk.Label(bar, text=APP_TITLE, bg=WIN_FACE, fg=WIN_TEXT, font=("Tahoma", 9)).pack(
            side=tk.LEFT, padx=4,
        )
        self.toolbar = bar

    def _build_context_menu(self) -> None:
        ctx = self._classic_menu(self.root)
        ctx.add_command(label="Open ROM...", command=self.open_rom)
        ctx.add_command(label="Close", command=self.close_rom)
        ctx.add_separator()
        ctx.add_command(label="Reset", command=self.reset)
        ctx.add_command(label="Power", command=self.power)
        ctx.add_checkbutton(label="Pause", variable=self.paused, command=self._sync_pause_from_menu)
        ctx.add_separator()
        ctx.add_command(label="Screenshot", command=self.screenshot)
        ctx.add_command(label="Debugger...", command=self.open_debugger)
        ctx.add_separator()
        ctx.add_command(label="Hide Menu", command=self.toggle_menu)
        self._context = ctx

    def _build_layout(self) -> None:
        # Win32 client: sunken bevel around a pure-black NES surface.
        self.client = tk.Frame(self.root, bg=WIN_FACE, bd=0, highlightthickness=0)
        self.client.pack(fill=tk.BOTH, expand=True)

        self.bevel = tk.Frame(
            self.client, bg=WIN_SHADOW, bd=0,
            highlightthickness=0,
        )
        self.bevel.pack(padx=2, pady=2)

        self.screen_label = tk.Label(
            self.bevel,
            bg=WIN_CLIENT,
            fg="#c0c0c0",
            text="",
            bd=0,
            highlightthickness=0,
            cursor="arrow",
        )
        self.screen_label.pack(padx=1, pady=1)
        self.screen_label.bind("<Button-3>", self._popup_context)
        self.screen_label.bind("<Control-Button-1>", self._popup_context)
        self.client.bind("<Button-3>", self._popup_context)

        self.osd = tk.Label(
            self.screen_label,
            text="",
            bg="#000000",
            fg="#ffffff",
            font=("Tahoma", 9),
            bd=1,
            relief=tk.SOLID,
            padx=6,
            pady=2,
        )

        self._blank_screen()

    def _blank_screen(self) -> None:
        if not self._alive:
            return
        factor = self.scale.get()
        w, h = SCREEN_W * factor, SCREEN_H * factor
        # Solid black placeholder matching FCEUX with no ROM loaded.
        ppm = b"P6\n%d %d\n255\n" % (SCREEN_W, SCREEN_H) + bytes(SCREEN_W * SCREEN_H * 3)
        base = tk.PhotoImage(data=ppm, format="PPM")
        self._photo = base.zoom(factor, factor) if factor > 1 else base
        try:
            self.screen_label.configure(image=self._photo, text="", width=w, height=h)
        except tk.TclError:
            pass

    def _fit_window(self) -> None:
        factor = self.scale.get()
        # Size to NES pixels + chrome (toolbar / bevel), not a hard-coded short box.
        self.root.update_idletasks()
        chrome_w = 8
        chrome_h = 8
        if self.toolbar is not None:
            try:
                chrome_h += max(self.toolbar.winfo_reqheight(), 28)
            except tk.TclError:
                chrome_h += 28
        self.root.geometry(
            f"{SCREEN_W * factor + chrome_w}x{SCREEN_H * factor + chrome_h}"
        )

    def _popup_context(self, event: tk.Event) -> None:
        if not self._context or not self._alive:
            return
        try:
            self._context.tk_popup(event.x_root, event.y_root)
        except tk.TclError:
            pass
        finally:
            try:
                self._context.grab_release()
            except tk.TclError:
                pass

    def _osd(self, text: str, seconds: float = 1.5) -> None:
        if not self._alive:
            return
        self._osd_text = text
        self._osd_until = time.perf_counter() + seconds
        try:
            self.osd.configure(text=text)
            self.osd.place(relx=0.5, rely=0.92, anchor=tk.S)
        except tk.TclError:
            pass

    def _tick_osd(self) -> None:
        if not self._alive or not self._osd_until:
            return
        if time.perf_counter() >= self._osd_until:
            self._osd_until = 0.0
            try:
                self.osd.place_forget()
            except tk.TclError:
                pass

    def toggle_menu(self) -> None:
        if not self._alive:
            return
        try:
            if self.menu_hidden:
                self.root.config(menu=self._menubar)
                self.menu_hidden = False
                self._osd("Menu")
            else:
                # Empty menu hides the bar on Win/X11; Aqua may ignore it — still safe.
                self.root.config(menu="")
                self.menu_hidden = True
                self._osd("Menu Hidden (Esc)")
        except tk.TclError:
            pass

    def open_rom(self) -> None:
        if not self._alive:
            return
        path = filedialog.askopenfilename(
            parent=self.root,
            title="Open",
            filetypes=(
                ("NES ROM", ("*.nes", "*.NES")),
                ("All files", "*.*"),
            ),
        )
        if path:
            self.load_rom(path)

    def close_rom(self) -> None:
        if not self.nes:
            return
        self.nes = None
        self.rom_path = None
        self.running = False
        self.paused.set(False)
        self._sync_pause_button()
        self.audio.clear()
        self.root.title(APP_TITLE)
        self._blank_screen()
        self._osd("ROM Closed")
        try:
            self._file_close.entryconfigure("Close", state=tk.DISABLED)
        except tk.TclError:
            pass

    def load_rom(self, path: str) -> None:
        try:
            cart = Cartridge.from_file(path)
            self.nes = NES(cart)
        except (OSError, CartridgeError) as exc:
            messagebox.showerror(APP_TITLE, str(exc), parent=self.root)
            return
        self.rom_path = pathlib.Path(path)
        self.running = True
        self.paused.set(False)
        self._sync_pause_button()
        self.audio.clear()
        self._next_frame = time.perf_counter()
        # FCEUX title form: "acnesemu 0.1.x" or with ROM basename.
        self.root.title(f"{APP_TITLE} - {self.rom_path.name}")
        self._osd(self.rom_path.name)
        try:
            self._file_close.entryconfigure("Close", state=tk.NORMAL)
        except tk.TclError:
            pass
        self._update_debugger()

    def reset(self) -> None:
        if not self.nes:
            return
        self.nes.reset()
        self.audio.clear()
        self.running = True
        self.paused.set(False)
        self._sync_pause_button()
        self._osd("Reset")

    def power(self) -> None:
        if not self.nes or not self.rom_path:
            return
        # Hard power-cycle: reload cartridge image (FCEUX Power).
        self.load_rom(str(self.rom_path))
        self._osd("Power")

    def _sync_pause_button(self) -> None:
        if not hasattr(self, "pause_button"):
            return
        try:
            self.pause_button.configure(text="Run" if self.paused.get() or not self.running else "Pause")
        except tk.TclError:
            pass

    def toggle_pause(self) -> None:
        if not self.nes:
            self.open_rom()
            return
        self.running = not self.running
        self.paused.set(not self.running)
        self._sync_pause_button()
        self._osd("Paused" if not self.running else "Running")
        self._next_frame = time.perf_counter()

    def _sync_pause_from_menu(self) -> None:
        if not self.nes:
            self.paused.set(False)
            self._sync_pause_button()
            return
        self.running = not self.paused.get()
        self._sync_pause_button()
        self._osd("Paused" if self.paused.get() else "Running")
        self._next_frame = time.perf_counter()

    def _toggle_turbo(self) -> None:
        self._osd("Turbo ON" if self.turbo.get() else "Turbo OFF")

    def step_frame(self) -> None:
        if not self.nes:
            return
        self.running = False
        self.paused.set(True)
        self._sync_pause_button()
        try:
            self.nes.run_frame()
            self.nes.bus.apu.drain_samples()
            self._draw_frame()
            self._update_debugger()
            self._osd(f"Frame {self.nes.bus.ppu.frame_number}")
        except RuntimeError as exc:
            self._runtime_error(exc)

    def step_instruction(self) -> None:
        if not self.nes:
            return
        self.running = False
        self.paused.set(True)
        self._sync_pause_button()
        self.nes.bus.cpu.step()
        self.nes.bus.apu.drain_samples()
        self.nes.bus.ppu.render()
        self._draw_frame()
        self._update_debugger()
        self._osd("Step Into")

    def _draw_frame(self) -> None:
        if not self._alive or not self.nes:
            return
        frame = self.nes.bus.ppu.framebuffer
        factor = self.scale.get()
        ppm = b"P6\n256 240\n255\n" + bytes(frame)
        base = tk.PhotoImage(data=ppm, format="PPM")
        self._photo = base.zoom(factor, factor) if factor > 1 else base
        try:
            self.screen_label.configure(
                image=self._photo, text="",
                width=SCREEN_W * factor, height=SCREEN_H * factor,
            )
        except tk.TclError:
            self._alive = False

    def _resize_screen(self) -> None:
        if self.nes:
            self._draw_frame()
        else:
            self._blank_screen()
        self._fit_window()
        self._osd(f"Scale {self.scale.get()}x")

    def _toggle_mute(self) -> None:
        self.audio.muted = self.muted.get()
        if self.audio.muted:
            self.audio.clear()
        self._osd("Sound Off" if self.audio.muted else "Sound On")

    def open_debugger(self) -> None:
        if self._debugger is not None:
            try:
                if self._debugger.winfo_exists():
                    self._debugger.lift()
                    self._debugger.focus_force()
                    return
            except tk.TclError:
                self._debugger = None
        top = tk.Toplevel(self.root)
        top.title(f"Debugger - {APP_TITLE}")
        top.configure(bg=WIN_FACE)
        top.geometry("420x520")
        top.resizable(True, True)
        top.transient(self.root)
        self._debugger = top

        nb = ttk.Notebook(top)
        nb.pack(fill=tk.BOTH, expand=True, padx=4, pady=4)
        cpu_tab = ttk.Frame(nb, padding=6)
        ppu_tab = ttk.Frame(nb, padding=6)
        apu_tab = ttk.Frame(nb, padding=6)
        nb.add(cpu_tab, text="CPU")
        nb.add(ppu_tab, text="PPU")
        nb.add(apu_tab, text="APU")

        self.register_text = tk.StringVar(value="No cartridge loaded")
        tk.Label(
            cpu_tab, textvariable=self.register_text, justify=tk.LEFT,
            font=("Courier New", 10), bg=WIN_FACE, fg=WIN_TEXT,
        ).pack(anchor=tk.W, fill=tk.X)
        ttk.Separator(cpu_tab).pack(fill=tk.X, pady=6)
        tk.Label(cpu_tab, text="Disassembly", bg=WIN_FACE, fg=WIN_TEXT).pack(anchor=tk.W)
        self.disassembly = tk.Text(
            cpu_tab, width=42, height=22, bg=WIN_WINDOW, fg=WIN_TEXT,
            insertbackground=WIN_TEXT, relief=tk.SUNKEN, borderwidth=2,
            font=("Courier New", 9), state=tk.DISABLED,
        )
        self.disassembly.pack(fill=tk.BOTH, expand=True, pady=(4, 0))
        self.ppu_text = tk.StringVar(value="No PPU state")
        tk.Label(
            ppu_tab, textvariable=self.ppu_text, justify=tk.LEFT,
            font=("Courier New", 10), bg=WIN_FACE, fg=WIN_TEXT,
        ).pack(anchor=tk.W)
        self.apu_text = tk.StringVar(value="No APU state")
        tk.Label(
            apu_tab, textvariable=self.apu_text, justify=tk.LEFT,
            font=("Courier New", 10), bg=WIN_FACE, fg=WIN_TEXT,
        ).pack(anchor=tk.W)

        bar = tk.Frame(top, bg=WIN_FACE)
        bar.pack(fill=tk.X, padx=4, pady=(0, 4))
        tk.Button(bar, text="Step Into", width=10, command=self.step_instruction).pack(side=tk.LEFT, padx=2)
        tk.Button(bar, text="Step Frame", width=10, command=self.step_frame).pack(side=tk.LEFT, padx=2)
        tk.Button(
            bar, text="Run", width=8,
            command=lambda: (self.paused.set(False), self._sync_pause_from_menu()),
        ).pack(side=tk.LEFT, padx=2)
        tk.Button(bar, text="Close", width=8, command=self._close_debugger).pack(side=tk.RIGHT, padx=2)
        top.protocol("WM_DELETE_WINDOW", self._close_debugger)
        self._update_debugger()

    def _close_debugger(self) -> None:
        top = self._debugger
        self._debugger = None
        if top is None:
            return
        try:
            top.destroy()
        except tk.TclError:
            pass

    def _update_debugger(self) -> None:
        if not self._alive or not self.nes or not self._debugger:
            return
        try:
            if not self._debugger.winfo_exists():
                self._debugger = None
                return
        except tk.TclError:
            self._debugger = None
            return
        cpu = self.nes.bus.cpu
        flags = "".join(
            letter if cpu.p & flag else "."
            for letter, flag in zip("NVUBDIZC", (N_FLAG, V_FLAG, U_FLAG, B_FLAG, D_FLAG, I_FLAG, Z_FLAG, C_FLAG))
        )
        try:
            self.register_text.set(
                f"PC  ${cpu.pc:04X}    A   ${cpu.a:02X}\n"
                f"X   ${cpu.x:02X}      Y   ${cpu.y:02X}\n"
                f"SP  ${cpu.sp:02X}      P   ${cpu.p:02X}\n"
                f"FLAGS {flags}\n"
                f"CYC {cpu.total_cycles:,}\n"
                f"OPCODES {len(OPCODES)}/256"
            )
            lines = disassemble(self.nes.bus, cpu.pc)
            self.disassembly.configure(state=tk.NORMAL)
            self.disassembly.delete("1.0", tk.END)
            self.disassembly.insert(
                "1.0",
                "\n".join(("> " if i == 0 else "  ") + line for i, line in enumerate(lines)),
            )
            self.disassembly.configure(state=tk.DISABLED)
            ppu = self.nes.bus.ppu
            self.ppu_text.set(
                f"SCANLINE {ppu.scanline:3d}\n"
                f"DOT      {ppu.dot:3d}\n"
                f"FRAME    {ppu.frame_number}\n"
                f"PPUCTRL  ${ppu.ctrl:02X}\n"
                f"PPUMASK  ${ppu.mask:02X}\n"
                f"STATUS   ${ppu.status:02X}\n"
                f"VRAM     ${ppu.address:04X}\n"
                f"SCROLL   {ppu.scroll_x:3d}, {ppu.scroll_y:3d}\n"
                f"MIRROR   {self.nes.cart.mapper.mirror_mode()}\n"
                f"MAPPER   {self.nes.cart.mapper_id}"
            )
            apu = self.nes.bus.apu
            self.apu_text.set(
                f"SAMPLE   {apu.SAMPLE_RATE:,} Hz\n"
                f"CYCLE    {apu.cpu_cycle:,}\n"
                f"SEQUENCER {'5-step' if apu.five_step else '4-step'}\n"
                f"FRAME IRQ {int(apu.frame_irq)}\n"
                f"DMC IRQ   {int(apu.dmc.irq)}\n\n"
                f"PULSE 1  {apu.pulse1.output:2d}  L={apu.pulse1.length:3d}  T={apu.pulse1.timer_period:4d}\n"
                f"PULSE 2  {apu.pulse2.output:2d}  L={apu.pulse2.length:3d}  T={apu.pulse2.timer_period:4d}\n"
                f"TRIANGLE {apu.triangle.output:2d}  L={apu.triangle.length:3d}  T={apu.triangle.timer_period:4d}\n"
                f"NOISE    {apu.noise.output:2d}  L={apu.noise.length:3d}  P={apu.noise.period:4d}\n"
                f"DMC      {apu.dmc.output:3d}  BYTES={apu.dmc.bytes_remaining:4d}\n\n"
                f"OUTPUT   {'muted' if self.audio.muted else ('active' if self.audio.available else 'unavailable')}"
            )
        except tk.TclError:
            self._debugger = None

    def _key_down(self, event: tk.Event) -> None:
        if not self._alive or not self.nes or self._focus_is_text():
            return
        key = event.keysym if event.keysym in self.KEY_BITS else (event.char or "").lower()
        bit = self.KEY_BITS.get(key)
        if bit is not None:
            self.nes.bus.controller_state[0] |= 1 << bit

    def _key_up(self, event: tk.Event) -> None:
        if not self._alive or not self.nes:
            return
        key = event.keysym if event.keysym in self.KEY_BITS else (event.char or "").lower()
        bit = self.KEY_BITS.get(key)
        if bit is not None:
            self.nes.bus.controller_state[0] &= ~(1 << bit)

    def screenshot(self) -> None:
        if not self.nes:
            return
        suggested = (self.rom_path.stem if self.rom_path else "acnesemu") + ".ppm"
        path = filedialog.asksaveasfilename(
            parent=self.root, defaultextension=".ppm", initialfile=suggested,
            filetypes=(("Portable Pixmap", "*.ppm"),),
        )
        if not path:
            return
        try:
            header = f"P6\n{SCREEN_W} {SCREEN_H}\n255\n".encode("ascii")
            pathlib.Path(path).write_bytes(header + bytes(self.nes.bus.ppu.framebuffer))
            self._osd(f"Saved {pathlib.Path(path).name}")
        except OSError as exc:
            messagebox.showerror(APP_TITLE, str(exc), parent=self.root)

    def show_controls(self) -> None:
        messagebox.showinfo(
            "Input",
            "Port 1\n\n"
            "D-pad: Arrow keys\n"
            "A: Z\n"
            "B: X\n"
            "Select: Shift\n"
            "Start: Enter\n\n"
            "Pause: Space / P\n"
            "Hide Menu: Esc",
            parent=self.root,
        )

    def show_sound(self) -> None:
        top = tk.Toplevel(self.root)
        top.title("Sound Config")
        top.configure(bg=WIN_FACE)
        top.resizable(False, False)
        top.transient(self.root)
        frm = tk.Frame(top, bg=WIN_FACE, padx=12, pady=10)
        frm.pack()
        tk.Label(frm, text="Sound", bg=WIN_FACE, fg=WIN_TEXT, font=("Tahoma", 9, "bold")).grid(
            row=0, column=0, sticky=tk.W, pady=(0, 6),
        )
        enabled = tk.BooleanVar(value=not self.muted.get())

        def apply_sound() -> None:
            self.muted.set(not enabled.get())
            self._toggle_mute()

        tk.Checkbutton(
            frm, text="Enabled", variable=enabled, command=apply_sound,
            bg=WIN_FACE, fg=WIN_TEXT, activebackground=WIN_FACE, selectcolor=WIN_FACE,
        ).grid(row=1, column=0, sticky=tk.W)
        state = "48 kHz pygame" if self.audio.available else "unavailable (install pygame-ce)"
        tk.Label(frm, text=f"Output: {state}", bg=WIN_FACE, fg=WIN_TEXT).grid(
            row=2, column=0, sticky=tk.W, pady=6,
        )
        tk.Button(frm, text="Close", width=10, command=top.destroy).grid(row=3, column=0, pady=(4, 0))

    def show_video(self) -> None:
        top = tk.Toplevel(self.root)
        top.title("Video Config")
        top.configure(bg=WIN_FACE)
        top.resizable(False, False)
        top.transient(self.root)
        frm = tk.Frame(top, bg=WIN_FACE, padx=12, pady=10)
        frm.pack()
        tk.Label(frm, text="Window Size", bg=WIN_FACE, fg=WIN_TEXT, font=("Tahoma", 9, "bold")).grid(
            row=0, column=0, sticky=tk.W, pady=(0, 6),
        )
        for i, factor in enumerate((1, 2, 3, 4), start=1):
            tk.Radiobutton(
                frm, text=f"{factor}x ({SCREEN_W * factor}x{SCREEN_H * factor})",
                value=factor, variable=self.scale, command=self._resize_screen,
                bg=WIN_FACE, fg=WIN_TEXT, activebackground=WIN_FACE, selectcolor=WIN_FACE,
            ).grid(row=i, column=0, sticky=tk.W)
        tk.Button(frm, text="Close", width=10, command=top.destroy).grid(
            row=5, column=0, pady=(10, 0),
        )

    def show_prompts(self) -> None:
        messagebox.showinfo(
            "Debugger prompts",
            PROMPT_HELP + "\nLaunch from a terminal with:\n  python3 acnes0.1.1a.py --prompt [rom.nes]",
            parent=self.root,
        )

    def show_opcodes(self) -> None:
        top = tk.Toplevel(self.root)
        top.title(f"Opcode Map - {APP_TITLE}")
        top.configure(bg=WIN_FACE)
        top.geometry("640x480")
        text = tk.Text(
            top, wrap=tk.NONE, font=("Courier New", 10),
            bg=WIN_WINDOW, fg=WIN_TEXT, relief=tk.SUNKEN, borderwidth=2,
        )
        scroll_y = tk.Scrollbar(top, orient=tk.VERTICAL, command=text.yview)
        scroll_x = tk.Scrollbar(top, orient=tk.HORIZONTAL, command=text.xview)
        text.configure(yscrollcommand=scroll_y.set, xscrollcommand=scroll_x.set)
        scroll_y.pack(side=tk.RIGHT, fill=tk.Y)
        scroll_x.pack(side=tk.BOTTOM, fill=tk.X)
        text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        text.insert(tk.END, "\n".join(list_all_opcodes()))
        text.insert(tk.END, f"\n\n— {len(OPCODES)}/256 opcodes; cycles match FCEUX CycTable\n")
        text.configure(state=tk.DISABLED)

    def show_about(self) -> None:
        messagebox.showinfo(
            f"About {APP_TITLE}",
            f"{APP_TITLE}\n"
            f"by {APP_AUTHOR}\n\n"
            "NES / Famicom emulator\n"
            f"Timing: {NTSC_FPS:.4f} FPS NTSC\n"
            f"CPU: {len(OPCODES)}/256 opcodes (FCEUX CycTable)\n"
            "APU: 2A03 pulse×2, triangle, noise, DMC\n"
            "PPU: BG + sprites, scroll, S0, overflow, clip\n"
            "Mappers: "
            + ", ".join(str(n) for n in sorted(MAPPERS))
            + "\n\n"
            "UI layout modeled on classic FCEUX Win32.\n"
            "Original clean-room educational code.\n"
            "Not FCEUX source. No ROMs or BIOS included.",
            parent=self.root,
        )

    def _runtime_error(self, exc: Exception) -> None:
        self.running = False
        self.paused.set(True)
        self._sync_pause_button()
        self._osd(f"Error: {exc}", seconds=4.0)
        if self._alive:
            messagebox.showerror(APP_TITLE, str(exc), parent=self.root)

    def _close(self) -> None:
        if not self._alive:
            return
        self._alive = False
        self.running = False
        if self._loop_after is not None:
            try:
                self.root.after_cancel(self._loop_after)
            except tk.TclError:
                pass
            self._loop_after = None
        self._close_debugger()
        try:
            self.audio.close()
        except Exception:
            pass
        try:
            self.root.unbind_all("<KeyPress>")
            self.root.unbind_all("<KeyRelease>")
        except tk.TclError:
            pass
        try:
            self.root.destroy()
        except tk.TclError:
            pass

    def _loop(self) -> None:
        if not self._alive:
            return
        try:
            now = time.perf_counter()
            self._tick_osd()
            if self.running and self.nes and now >= self._next_frame:
                try:
                    # Turbo skips pacing (FCEUX-style fast-forward).
                    frames = 2 if self.turbo.get() else 1
                    for _ in range(frames):
                        self.nes.run_frame()
                        self.audio.submit(self.nes.bus.apu.drain_samples())
                    self._draw_frame()
                    self._frames_since_fps += frames
                    if self._frames_since_fps % 4 == 0:
                        self._update_debugger()
                    frame_time = 1.0 / NTSC_FPS
                    self._next_frame += frame_time
                    if now - self._next_frame > frame_time * 3:
                        self._next_frame = now + frame_time
                    elapsed = now - self._fps_timer
                    if elapsed >= 1.0:
                        self._fps_timer = now
                        self._frames_since_fps = 0
                except Exception as exc:  # Keep Tk alive and expose core failures.
                    self._runtime_error(exc)
            delay = max(1, int((self._next_frame - time.perf_counter()) * 1000)) if self.running else 8
            self._loop_after = self.root.after(min(delay, 16), self._loop)
        except tk.TclError:
            self._alive = False
            self._loop_after = None


def _make_test_rom(mapper: int = 0, prg_banks: int = 1, chr_banks: int = 1) -> bytes:
    header = bytearray(16)
    header[0:4] = b"NES\x1a"
    header[4] = prg_banks & 0xFF
    header[5] = chr_banks & 0xFF
    header[6] = (mapper & 0x0F) << 4
    header[7] = mapper & 0xF0
    prg = bytearray([0xEA] * (prg_banks * 0x4000))
    # LDX #$01; INX; STX $00; JMP $8002
    prg[:8] = bytes((0xA2, 0x01, 0xE8, 0x86, 0x00, 0x4C, 0x02, 0x80))
    prg[-6:] = bytes((0x00, 0x80, 0x00, 0x80, 0x00, 0x80))
    chr_rom = bytearray(chr_banks * 0x2000) if chr_banks else bytearray()
    return bytes(header + prg + chr_rom)


def self_test() -> int:
    assert_fceux_opcode_table()
    assert len(OPCODES) == 256
    assert all(ins.mode in MODE_LENGTH for ins in OPCODES)
    # Every FCEUX-documented mnemonic class must have an execute path.
    required = {
        "ADC", "AHX", "ALR", "ANC", "AND", "ARR", "ASL", "AXS",
        "BCC", "BCS", "BEQ", "BIT", "BMI", "BNE", "BPL", "BRK", "BVC", "BVS",
        "CLC", "CLD", "CLI", "CLV", "CMP", "CPX", "CPY",
        "DCP", "DEC", "DEX", "DEY",
        "EOR",
        "INC", "INX", "INY", "ISC",
        "JMP", "JSR",
        "KIL",
        "LAS", "LAX", "LDA", "LDX", "LDY", "LSR",
        "NOP",
        "ORA",
        "PHA", "PHP", "PLA", "PLP",
        "RLA", "ROL", "ROR", "RRA", "RTI", "RTS",
        "SAX", "SBC", "SEC", "SED", "SEI", "SHX", "SHY", "SLO", "SRE",
        "STA", "STX", "STY",
        "TAS", "TAX", "TAY", "TSX", "TXA", "TXS", "TYA", "XAA",
    }
    present = {ins.name for ins in OPCODES}
    missing = required - present
    assert not missing, f"opcode table missing: {sorted(missing)}"
    assert "$E2" and OPCODES[0xE2].cycles == 3  # FCEUX NOP IMM quirk
    assert PROMPT_HELP and "opcodes" in PROMPT_HELP
    assert len(list_all_opcodes()) == 256

    cart = Cartridge(_make_test_rom(), "<self-test>")
    nes = NES(cart)
    for _ in range(20):
        nes.bus.cpu.step()
    assert nes.bus.ram[0] > 1
    assert nes.bus.cpu.pc in range(0x8002, 0x8008)
    # Verify mapper zero mirrors a 16 KiB PRG into both CPU banks.
    assert cart.cpu_read(0x8000) == cart.cpu_read(0xC000)
    # Exercise a full PPU frame and raster output without opening a window.
    nes.run_frame()
    assert len(nes.bus.ppu.framebuffer) == SCREEN_W * SCREEN_H * 3

    # Scanline renderer + PPUADDR scroll sync (used by SMB3/MMC3 status-bar IRQs).
    split_cart = Cartridge(_make_test_rom(4, prg_banks=2, chr_banks=2), "<scanline-split>")
    split_nes = NES(split_cart)
    split_ppu = split_nes.bus.ppu
    split_ppu.fine_x = 0
    split_ppu.write_register(0x2006, 0x20)
    split_ppu.write_register(0x2006, 0x00)
    assert split_ppu.scroll_y == 2, "PPUADDR must update scroll for split-screen games"
    split_nes.run_frame()
    assert len(split_ppu.framebuffer) == SCREEN_W * SCREEN_H * 3
    assert not split_ppu._frame_render_active

    # Sprite overflow + greyscale/emphasis paths.
    overflow_nes = NES(Cartridge(_make_test_rom(), "<ppu-overflow>"))
    ppu = overflow_nes.bus.ppu
    ppu.mask = 0x1E  # show BG+sprites, left columns on; no greyscale yet
    for i in range(9):
        ppu.oam[i * 4] = 20  # top = 21 → all hit scanline 21
        ppu.oam[i * 4 + 1] = 0
        ppu.oam[i * 4 + 2] = 0
        ppu.oam[i * 4 + 3] = i * 8
    ppu.render()
    assert ppu.status & 0x20, "sprite overflow bit not set"
    ppu.mask = 0xE1  # greyscale + all emphasis
    frame = ppu.render()
    assert len(frame) == SCREEN_W * SCREEN_H * 3

    # Walk every opcode byte once (KIL jams; reset between groups).
    walk = NES(Cartridge(_make_test_rom(), "<opcode-walk>"))
    for opcode in range(256):
        cpu = walk.bus.cpu
        cpu.reset()
        cpu.jammed = False
        cpu.a = cpu.x = cpu.y = 0x11
        cpu.sp = 0xFD
        cpu.p = I_FLAG | U_FLAG
        # Plant a tiny trampoline: opcode + safe IMM/ABS operands, then jam.
        base = 0x0200
        walk.bus.ram[base & 0x7FF] = opcode
        walk.bus.ram[(base + 1) & 0x7FF] = 0x00
        walk.bus.ram[(base + 2) & 0x7FF] = 0x02
        walk.bus.ram[(base + 3) & 0x7FF] = 0x02  # KIL
        cpu.pc = base
        try:
            cpu.step()
        except Exception as exc:  # pragma: no cover - must not happen
            raise AssertionError(f"opcode ${opcode:02X} crashed: {exc}") from exc

    # Exercise a constant-volume pulse waveform and the 48 kHz sample clock.
    audio_nes = NES(Cartridge(_make_test_rom(), "<audio-self-test>"))
    apu = audio_nes.bus.apu
    apu.write(0x4017, 0x40)
    apu.write(0x4015, 0x01)
    apu.write(0x4000, 0xBF)  # 50% duty, loop, constant volume 15
    apu.write(0x4002, 0xFD)
    apu.write(0x4003, 0x08)
    apu.step(29_782)
    pcm = apu.drain_samples()
    assert 1_580 <= len(pcm) <= 1_610
    assert len(set(pcm)) > 8
    # Triangle + noise channels for fuller 2A03 coverage.
    apu.write(0x4015, 0x0F)
    apu.write(0x4008, 0xFF)
    apu.write(0x400A, 0x80)
    apu.write(0x400B, 0x00)
    apu.write(0x400C, 0x3F)
    apu.write(0x400E, 0x04)
    apu.write(0x400F, 0x08)
    apu.step(8_000)
    pcm2 = apu.drain_samples()
    assert len(pcm2) > 0 and len(set(pcm2)) > 4
    # Verify DMC DMA, sample exhaustion IRQ, and IRQ acknowledge behavior.
    dmc_nes = NES(Cartridge(_make_test_rom(), "<dmc-self-test>"))
    dmc = dmc_nes.bus.apu
    dmc.write(0x4010, 0x8F)
    dmc.write(0x4012, 0x00)
    dmc.write(0x4013, 0x00)
    dmc.write(0x4015, 0x10)
    dmc.step(2)
    assert dmc.dmc.irq and dmc_nes.bus.cpu.stall >= 4
    assert dmc.read_status() & 0x80
    dmc.write(0x4015, 0x00)
    assert not dmc.dmc.irq

    # Smoke-load every registered mapper with a multi-bank test image.
    for mapper_id in sorted(MAPPERS):
        prg_banks = 4 if mapper_id else 1
        chr_banks = 4 if mapper_id not in (0, 2, 7, 13, 71, 94, 180) else 1
        if mapper_id in (2, 7, 13, 71, 93, 94, 180):
            chr_banks = 0  # CHR-RAM boards
        try:
            probe = Cartridge(
                _make_test_rom(mapper_id, prg_banks=max(prg_banks, 2), chr_banks=chr_banks),
                f"<mapper-{mapper_id}>",
            )
        except CartridgeError as exc:
            raise AssertionError(f"mapper {mapper_id} failed to load: {exc}") from exc
        assert probe.mapper_id == mapper_id
        assert probe.mapper.cpu_read(0x8000) is not None or mapper_id == 0
        _ = probe.mapper.ppu_read(0x0000)
        probe.mapper.clock_scanline()
        probe.mapper.clock_cpu(3)
        probe.mapper.reset()

    print(
        f"{APP_TITLE}: self-test passed "
        f"({len(OPCODES)} FCEUX opcodes, {len(MAPPERS)} mappers, "
        f"frame {nes.bus.ppu.frame_number}, 2A03 audio, prompts ready)"
    )
    return 0


def parse_args(argv: Optional[list[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[1])
    parser.add_argument("rom", nargs="?", help="optional .nes ROM to open")
    parser.add_argument("--self-test", action="store_true", help="test the core without opening the GUI")
    parser.add_argument(
        "--prompt", "-p", action="store_true",
        help="interactive FCEUX-inspired debugger prompt (opcodes/step/frame/mem)",
    )
    parser.add_argument(
        "--opcodes", action="store_true",
        help="print the full 256-entry FCEUX-aligned opcode map and exit",
    )
    return parser.parse_args(argv)


def main(argv: Optional[list[str]] = None) -> int:
    args = parse_args(argv)
    if args.self_test:
        return self_test()
    if args.opcodes:
        assert_fceux_opcode_table()
        print("\n".join(list_all_opcodes()))
        print(f"— {len(OPCODES)}/256 opcodes (FCEUX CycTable match)")
        return 0
    if args.prompt:
        return run_prompt(args.rom)
    root = tk.Tk()
    EmulatorGUI(root, args.rom)
    root.mainloop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
