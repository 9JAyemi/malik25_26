#!/usr/bin/env python3
"""
Parse VCD files from JasperGold CEX dumps and produce ASCII tables and CSV files.

Usage:
  # Parse a single VCD file:
  python parse_vcd_cex.py path/to/cex.vcd

  # Parse all VCD files in a directory:
  python parse_vcd_cex.py path/to/cex_vcd/

  # Specify output directory (default: same dir as input):
  python parse_vcd_cex.py path/to/cex.vcd -o output_dir/

  # CSV only or ASCII only:
  python parse_vcd_cex.py path/to/cex.vcd --csv-only
  python parse_vcd_cex.py path/to/cex.vcd --ascii-only
"""

import argparse
import csv
import os
import re
import sys
from pathlib import Path


def parse_vcd(filepath: str) -> dict:
    """Parse a VCD file and return structured signal data.

    Returns:
        dict with keys:
            - 'signals': {var_id: {'name': str, 'width': int, 'scope': str}}
            - 'timescale': str
            - 'events': sorted list of (time, var_id, value)
    """
    signals = {}      # var_id -> {name, width, scope}
    events = []        # [(time, var_id, value), ...]
    timescale = ""
    scope_stack = []

    with open(filepath, "r") as f:
        in_defs = True
        current_time = 0

        for line in f:
            line = line.strip()
            if not line:
                continue

            # --- Header / definition section ---
            if line.startswith("$timescale"):
                # May be on same line: $timescale 1ns $end
                m = re.search(r'\$timescale\s+(.+?)\s*\$end', line)
                if m:
                    timescale = m.group(1).strip()
                continue

            if line.startswith("$scope"):
                m = re.match(r'\$scope\s+\w+\s+(\S+)\s+\$end', line)
                if m:
                    scope_stack.append(m.group(1))
                continue

            if line.startswith("$upscope"):
                if scope_stack:
                    scope_stack.pop()
                continue

            if line.startswith("$var"):
                # $var wire 1 ! A $end
                m = re.match(
                    r'\$var\s+\w+\s+(\d+)\s+(\S+)\s+(\S+)(?:\s+\[.*?\])?\s+\$end',
                    line,
                )
                if m:
                    width = int(m.group(1))
                    var_id = m.group(2)
                    name = m.group(3)
                    scope = ".".join(scope_stack) if scope_stack else ""
                    signals[var_id] = {
                        "name": name,
                        "width": width,
                        "scope": scope,
                    }
                continue

            if line.startswith("$enddefinitions"):
                in_defs = False
                continue

            if line.startswith("$"):
                # Skip other VCD keywords ($comment, $date, $version, etc.)
                continue

            if in_defs:
                continue

            # --- Value change section ---
            # Timestamp: #<number>
            if line.startswith("#"):
                m = re.match(r"#(\d+)", line)
                if m:
                    current_time = int(m.group(1))
                continue

            # Scalar value change: 0! 1! x! z!
            if len(line) >= 2 and line[0] in "01xXzZ":
                val = line[0]
                var_id = line[1:]
                if var_id in signals:
                    events.append((current_time, var_id, val))
                continue

            # Vector value change: b<bits> <var_id>
            m = re.match(r"([bB])([01xXzZ]+)\s+(\S+)", line)
            if m:
                val = m.group(2)
                var_id = m.group(3)
                if var_id in signals:
                    events.append((current_time, var_id, val))
                continue

            # Real value change: r<float> <var_id>
            m = re.match(r"[rR](\S+)\s+(\S+)", line)
            if m:
                val = m.group(1)
                var_id = m.group(2)
                if var_id in signals:
                    events.append((current_time, var_id, val))
                continue

    events.sort(key=lambda x: x[0])
    return {"signals": signals, "timescale": timescale, "events": events}


def build_trace_table(parsed: dict) -> tuple:
    """Build a table of signal values at each timestep.

    Returns:
        (header_names, rows) where:
            header_names = ['Time', 'sig1', 'sig2', ...]
            rows = [[time, val1, val2, ...], ...]
    """
    signals = parsed["signals"]
    events = parsed["events"]

    if not signals:
        return [], []

    # Collect all unique timestamps
    timestamps = sorted(set(t for t, _, _ in events))
    if not timestamps:
        return [], []

    # Order signals: group by scope, then alphabetically by name
    var_ids = sorted(
        signals.keys(),
        key=lambda vid: (signals[vid]["scope"], signals[vid]["name"]),
    )

    # Build display names (scope.name if scope exists)
    display_names = []
    for vid in var_ids:
        s = signals[vid]
        if s["scope"]:
            display_names.append(f"{s['scope']}.{s['name']}")
        else:
            display_names.append(s["name"])

    # Track current value for each signal
    current_vals = {vid: "x" for vid in var_ids}

    # Group events by timestamp
    events_by_time = {}
    for t, vid, val in events:
        events_by_time.setdefault(t, []).append((vid, val))

    header = ["Time"] + display_names
    rows = []

    for t in timestamps:
        # Apply all changes at this timestamp
        if t in events_by_time:
            for vid, val in events_by_time[t]:
                if vid in current_vals:
                    current_vals[vid] = val

        row = [str(t)]
        for vid in var_ids:
            row.append(current_vals[vid])
        rows.append(row)

    return header, rows


def format_ascii_table(header: list, rows: list) -> str:
    """Format header and rows into an aligned ASCII table."""
    if not header:
        return "(no signals found)\n"

    # Calculate column widths
    col_widths = [len(h) for h in header]
    for row in rows:
        for i, cell in enumerate(row):
            col_widths[i] = max(col_widths[i], len(cell))

    def fmt_row(cells):
        parts = []
        for i, cell in enumerate(cells):
            parts.append(cell.ljust(col_widths[i]))
        return " | ".join(parts)

    separator = "-+-".join("-" * w for w in col_widths)

    lines = [fmt_row(header), separator]
    for row in rows:
        lines.append(fmt_row(row))

    return "\n".join(lines) + "\n"


def write_csv(header: list, rows: list, filepath: str):
    """Write header and rows to a CSV file."""
    with open(filepath, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(header)
        writer.writerows(rows)


def process_vcd_file(
    vcd_path: str, out_dir: str, write_ascii: bool = True, write_csv_file: bool = True
):
    """Process a single VCD file: parse, generate ASCII table and/or CSV."""
    vcd_path = os.path.abspath(vcd_path)
    stem = Path(vcd_path).stem

    print(f"Parsing: {vcd_path}")
    parsed = parse_vcd(vcd_path)

    n_signals = len(parsed["signals"])
    n_events = len(parsed["events"])
    print(f"  Signals: {n_signals}, Events: {n_events}, Timescale: {parsed['timescale']}")

    if n_signals == 0:
        print("  WARN: No signals found in VCD file")
        return

    header, rows = build_trace_table(parsed)

    if not rows:
        print("  WARN: No value changes found")
        return

    print(f"  Timesteps: {len(rows)}")

    os.makedirs(out_dir, exist_ok=True)

    if write_ascii:
        ascii_table = format_ascii_table(header, rows)
        txt_path = os.path.join(out_dir, f"{stem}_cex_table.txt")
        with open(txt_path, "w") as f:
            f.write(f"# CEX Trace: {Path(vcd_path).name}\n")
            if parsed["timescale"]:
                f.write(f"# Timescale: {parsed['timescale']}\n")
            f.write(f"# Signals: {n_signals}, Timesteps: {len(rows)}\n\n")
            f.write(ascii_table)
        print(f"  ASCII table -> {txt_path}")

        # Also print to stdout for convenience
        print()
        print(ascii_table)

    if write_csv_file:
        csv_path = os.path.join(out_dir, f"{stem}_cex_table.csv")
        write_csv(header, rows, csv_path)
        print(f"  CSV table   -> {csv_path}")


def main():
    parser = argparse.ArgumentParser(
        description="Parse JasperGold CEX VCD files into ASCII and CSV tables."
    )
    parser.add_argument(
        "input",
        help="VCD file or directory containing VCD files",
    )
    parser.add_argument(
        "-o", "--output-dir",
        default=None,
        help="Output directory for tables (default: same as input)",
    )
    parser.add_argument(
        "--csv-only",
        action="store_true",
        help="Only generate CSV output",
    )
    parser.add_argument(
        "--ascii-only",
        action="store_true",
        help="Only generate ASCII table output",
    )
    args = parser.parse_args()

    input_path = os.path.abspath(args.input)
    write_ascii = not args.csv_only
    write_csv_out = not args.ascii_only

    if os.path.isfile(input_path):
        vcd_files = [input_path]
        default_out = os.path.dirname(input_path)
    elif os.path.isdir(input_path):
        vcd_files = sorted(
            str(p) for p in Path(input_path).glob("*.vcd")
        )
        if not vcd_files:
            print(f"No .vcd files found in {input_path}")
            sys.exit(1)
        default_out = input_path
    else:
        print(f"Input not found: {input_path}")
        sys.exit(1)

    out_dir = args.output_dir or default_out

    print(f"Processing {len(vcd_files)} VCD file(s)")
    print(f"Output dir: {out_dir}\n")

    for vcd in vcd_files:
        process_vcd_file(vcd, out_dir, write_ascii=write_ascii, write_csv_file=write_csv_out)
        print()

    print("Done.")


if __name__ == "__main__":
    main()
