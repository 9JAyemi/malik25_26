#!/usr/bin/env python3
"""
Convert bare-property SVA (adapter_vert format) to module-wrapped SVA
with explicit assert statements, suitable for JasperGold verification.

Input SVA format (bare, no module):
    property NAME; @(posedge clk) A |-> B; endproperty

Output SVA format (module-wrapped):
    module <DUT>_sva (
        input logic clk,
        input logic A, B, ...
    );
    property NAME; @(posedge clk) A |-> B; endproperty
    assert property (NAME);
    endmodule

Exit codes:
  0 - conversion performed, output written
  1 - SVA already has module wrapper (no conversion needed)
  2 - error
"""

import re
import sys
import os

SV_KEYWORDS = {
    'property', 'endproperty', 'assert', 'assume', 'cover', 'sequence',
    'endsequence', 'posedge', 'negedge', 'edge', 'always', 'module',
    'endmodule', 'input', 'output', 'inout', 'wire', 'reg', 'logic',
    'begin', 'end', 'if', 'else', 'case', 'casez', 'casex', 'endcase',
    'forever', 'repeat', 'while', 'for', 'foreach', 'default', 'assign',
    'initial', 'always_ff', 'always_comb', 'always_latch', 'not', 'and',
    'or', 'nand', 'nor', 'xor', 'xnor', 'buf', 'bufif0', 'bufif1',
    'disable', 'iff', 'throughout', 'until', 'within', 'intersect',
    'first_match', 'strong', 'weak', 'true', 'false', 'supply0', 'supply1',
    'parameter', 'localparam', 'integer', 'bit', 'byte', 'shortint',
    'int', 'longint', 'real', 'time', 'string', 'void', 'enum', 'struct',
    'union', 'typedef', 'import', 'export', 'package', 'endpackage',
    'interface', 'endinterface', 'modport', 'clocking', 'endclocking',
    'generate', 'endgenerate', 'genvar', 'signed', 'unsigned',
    'tri', 'tri0', 'tri1', 'wand', 'wor', 'trireg', 'highz0', 'highz1',
    'pull0', 'pull1', 'small', 'medium', 'large', 'scalared', 'vectored',
    'deassign', 'force', 'release', 'fork', 'join', 'join_any', 'join_none',
    'wait', 'wait_order', 'expect', 'reject_on', 'sync_reject_on',
    'accept_on', 'sync_accept_on', 'eventually', 'nexttime', 's_nexttime',
    'until_with', 's_until', 's_until_with', 'implies', 's_always',
    's_eventually', 'global_clocking', 'default', 'clocking',
}

_NUMERIC_RE = re.compile(r'^\d')


def strip_comments(text):
    text = re.sub(r'//[^\n]*', '', text)
    text = re.sub(r'/\*.*?\*/', '', text, flags=re.DOTALL)
    return text


def parse_module(module_v):
    """
    Extract top module name and all non-supply signal names
    (ports + internal wire/reg/logic).
    Returns (top_name, set_of_signal_names).
    """
    with open(module_v, encoding='utf-8', errors='replace') as f:
        raw = f.read()
    text = strip_comments(raw)

    m = re.search(r'\bmodule\s+(\w+)', text)
    top = m.group(1) if m else 'unknown'

    signals = set()

    # Port names from port list: module NAME (...port list...);
    port_m = re.search(
        r'module\s+\w+\s*(?:#\s*\([^)]*\)\s*)?\(([^)]*)\)\s*;', text
    )
    if port_m:
        for tok in re.findall(r'\b([A-Za-z_]\w*)\b', port_m.group(1)):
            signals.add(tok)

    # Explicit input/output/inout/wire/reg/logic declarations
    for decl in re.finditer(
        r'\b(?:input|output|inout|wire|reg|logic)\b'
        r'(?:\s+(?:signed|unsigned))?'
        r'(?:\s*\[\s*[^\]]*\])?\s*'
        r'([A-Za-z_]\w*)',
        text
    ):
        signals.add(decl.group(1))

    # Remove supply nets
    for decl in re.finditer(r'\b(?:supply0|supply1)\s+([\w\s,]+);', text):
        for name in re.findall(r'\b([A-Za-z_]\w*)\b', decl.group(1)):
            signals.discard(name)

    signals -= SV_KEYWORDS
    signals = {s for s in signals if not _NUMERIC_RE.match(s)}
    return top, signals


def parse_bare_sva(sva_file):
    """
    Return list of (name, full_text) for each property declaration,
    or None if the file already has a module wrapper.
    """
    with open(sva_file, encoding='utf-8', errors='replace') as f:
        text = f.read()

    if re.search(r'\bmodule\b', text, re.IGNORECASE):
        return None  # already module-wrapped

    props = []
    for m in re.finditer(
        r'\bproperty\s+(\w+)\s*;(.*?)endproperty',
        text, re.DOTALL
    ):
        props.append((m.group(1), m.group(0)))
    return props


def deduplicate(properties):
    """Rename duplicate property names: NAME → NAME_2, NAME_3, ..."""
    seen = {}
    result = []
    for name, body in properties:
        if name not in seen:
            seen[name] = 1
            result.append((name, body))
        else:
            seen[name] += 1
            new_name = f"{name}_{seen[name]}"
            new_body = re.sub(
                r'(\bproperty\s+)' + re.escape(name) + r'\b',
                r'\g<1>' + new_name,
                body, count=1
            )
            result.append((new_name, new_body))
    return result


def referenced_signals(properties):
    """Extract identifiers referenced in property bodies (heuristic)."""
    all_text = ' '.join(body for _, body in properties)
    tokens = set(re.findall(r'\b([A-Za-z_]\w*)\b', all_text))
    tokens -= SV_KEYWORDS
    return {t for t in tokens if not _NUMERIC_RE.match(t)}


def build_sva_module(top_name, dut_signals, props, ref_signals):
    """Build a module-wrapped SVA string."""
    prop_names = {name for name, _ in props}

    # Ports = DUT signals that appear in the SVA + any SVA-only signals
    # (e.g. clocks not in DUT). Exclude property names themselves.
    dut_matched  = sorted(dut_signals & ref_signals - prop_names)
    extra_sva    = sorted(ref_signals - dut_signals - prop_names)
    ports = dut_matched + extra_sva

    lines = [f"module {top_name}_sva ("]
    if ports:
        decls = [f"    input logic {p}" for p in ports]
        lines.append(",\n".join(decls))
    lines.append(");")
    lines.append("")

    for name, body in props:
        lines.append(body.strip())
        lines.append(f"assert property ({name});")
        lines.append("")

    lines.append("endmodule")
    return "\n".join(lines)


def main():
    if len(sys.argv) != 4:
        print(
            f"Usage: {sys.argv[0]} <module.v> <sva.sv> <output_sva.sv>",
            file=sys.stderr
        )
        sys.exit(2)

    module_v, sva_sv, out_sv = sys.argv[1], sys.argv[2], sys.argv[3]

    props = parse_bare_sva(sva_sv)
    if props is None:
        # Already module-wrapped — nothing to do
        sys.exit(1)

    if not props:
        print(
            f"WARN: No property declarations found in {sva_sv}",
            file=sys.stderr
        )
        sys.exit(1)

    top, dut_signals = parse_module(module_v)
    props = deduplicate(props)
    ref = referenced_signals(props)

    result = build_sva_module(top, dut_signals, props, ref)

    out_dir = os.path.dirname(out_sv)
    if out_dir:
        os.makedirs(out_dir, exist_ok=True)
    with open(out_sv, 'w', encoding='utf-8') as f:
        f.write(result)

    print(
        f"INFO: fix_vert_sva: {len(props)} properties, "
        f"{len(dut_signals & ref)} DUT signals + "
        f"{len(ref - dut_signals)} extra → {out_sv}"
    )
    sys.exit(0)


if __name__ == '__main__':
    main()
