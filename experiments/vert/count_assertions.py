#!/usr/bin/env python3
"""
Count assertions in generated and syntax-passing SVA files.

Generated:   runs/inference/adapter_vert/<id>/sva.sv
Syntax pass: runs/inference/syntax_results/adapter_vert/ids/<id>/log.txt
             (only count SVAs from IDs whose log.txt contains PASSED)
"""

import os
import re
import argparse
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

# ── regex patterns ──────────────────────────────────────────────────────────
# Matches bare `property <name>` declarations (no assert/cover/assume prefix)
BARE_PROPERTY_RE  = re.compile(r'^\s*property\s+\w+', re.MULTILINE)
# Also count assert property / cover property / assume property
ASSERT_RE         = re.compile(r'\bassert\s+property\b', re.MULTILINE)
COVER_RE          = re.compile(r'\bcover\s+property\b',  re.MULTILINE)
ASSUME_RE         = re.compile(r'\bassume\s+property\b', re.MULTILINE)

PASS_RE = re.compile(r'PASSED.*Syntax check successful', re.IGNORECASE)


def count_properties_in_file(sv_path):
    """Return (bare_props, assert_props, cover_props, assume_props)."""
    try:
        text = open(sv_path).read()
    except FileNotFoundError:
        return 0, 0, 0, 0
    bare    = len(BARE_PROPERTY_RE.findall(text))
    asserts = len(ASSERT_RE.findall(text))
    covers  = len(COVER_RE.findall(text))
    assumes = len(ASSUME_RE.findall(text))
    return bare, asserts, covers, assumes


def scan_generated(base_dir):
    """Count properties across ALL generated SVA files."""
    totals = dict(bare=0, asserts=0, covers=0, assumes=0, ids=0, missing=0)

    if not os.path.isdir(base_dir):
        print(f"[WARN] Generated dir not found: {base_dir}")
        return totals

    for id_folder in sorted(os.listdir(base_dir)):
        sv_path = os.path.join(base_dir, id_folder, "sva.sv")
        if not os.path.isfile(sv_path):
            totals["missing"] += 1
            continue
        b, a, c, u = count_properties_in_file(sv_path)
        totals["bare"]    += b
        totals["asserts"] += a
        totals["covers"]  += c
        totals["assumes"] += u
        totals["ids"]     += 1

    return totals


def scan_syntax_passing(ids_dir, generated_base):
    """
    Find IDs whose log.txt says PASSED, then count properties in their sva.sv
    from the *generated* folder (since syntax_results may not copy the sv).
    Falls back to looking for sva.sv inside the syntax_results id folder.
    """
    totals = dict(bare=0, asserts=0, covers=0, assumes=0,
                  ids_checked=0, ids_passed=0, missing_sv=0)

    if not os.path.isdir(ids_dir):
        print(f"[WARN] Syntax ids dir not found: {ids_dir}")
        return totals

    for id_folder in sorted(os.listdir(ids_dir)):
        log_path = os.path.join(ids_dir, id_folder, "log.txt")
        if not os.path.isfile(log_path):
            continue
        totals["ids_checked"] += 1

        log_text = open(log_path).read()
        if not PASS_RE.search(log_text):
            continue  # failed syntax — skip
        totals["ids_passed"] += 1

        # Try generated folder first, then syntax_results id folder
        sv_path = os.path.join(generated_base, id_folder, "sva.sv")
        if not os.path.isfile(sv_path):
            sv_path = os.path.join(ids_dir, id_folder, "sva.sv")
        if not os.path.isfile(sv_path):
            totals["missing_sv"] += 1
            continue

        b, a, c, u = count_properties_in_file(sv_path)
        totals["bare"]    += b
        totals["asserts"] += a
        totals["covers"]  += c
        totals["assumes"] += u

    return totals


def report(label, t, syntax=False):
    print(f"\n{'='*60}")
    print(f"  {label}")
    print(f"{'='*60}")
    if syntax:
        print(f"  IDs checked          : {t['ids_checked']}")
        print(f"  IDs passed syntax    : {t['ids_passed']}")
        print(f"  Missing sva.sv       : {t['missing_sv']}")
    else:
        print(f"  IDs with sva.sv      : {t['ids']}")
        print(f"  Missing sva.sv       : {t['missing']}")
    print(f"  Bare property decls  : {t['bare']}")
    print(f"  assert property      : {t['asserts']}")
    print(f"  cover  property      : {t['covers']}")
    print(f"  assume property      : {t['assumes']}")
    total_all = t['bare'] + t['asserts'] + t['covers'] + t['assumes']
    print(f"  TOTAL (all kinds)    : {total_all}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--generated", default=str(REPO_ROOT / "runs" / "inference" / "adapter_vert"),
                        help="Base dir of generated SVA (contains <id>/sva.sv)")
    parser.add_argument("--syntax-ids", default=str(REPO_ROOT / "runs" / "inference" / "syntax_results" / "adapter_vert" / "ids"),
                        help="Dir with <id>/log.txt for syntax results")
    args = parser.parse_args()

    gen   = scan_generated(args.generated)
    syn   = scan_syntax_passing(args.syntax_ids, args.generated)

    report("GENERATED (all 578 IDs)", gen, syntax=False)
    report("SYNTAX-PASSING IDs", syn, syntax=True)


if __name__ == "__main__":
    main()
