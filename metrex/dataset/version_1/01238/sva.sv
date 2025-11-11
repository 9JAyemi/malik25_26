// SVA for mux_4to1 and mux2to1. Bind these to the DUTs.
// Focus: functional equivalence, first/second-level correctness, X-safety, and concise coverage.

module mux2to1_sva (
  input logic a, b, sel,
  input logic y
);
  // Select must be known
  assert property (@(sel) !$isunknown(sel))
    else $error("mux2to1: sel is X/Z");

  // Functional check (combinational, allow delta ##0)
  assert property (@(a or b or sel or y) (!$isunknown(sel)) |-> ##0 (y === (sel ? b : a)))
    else $error("mux2to1: y != (sel?b:a)");

  // Coverage: both select values seen, and routing exercised
  cover property (@(sel) sel===1'b0);
  cover property (@(sel) sel===1'b1);

  cover property (@(a or sel or y) sel===1'b0 && $changed(a) ##0 (y===a));
  cover property (@(b or sel or y) sel===1'b1 && $changed(b) ##0 (y===b));
endmodule

bind mux2to1 mux2to1_sva u_mux2to1_sva (.*);


module mux_4to1_sva (
  input  logic [3:0] a, b, c, d,
  input  logic [1:0] sel,
  input  logic [3:0] y,
  input  logic [3:0] ab_sel, cd_sel
);
  // Select must be known (both bits)
  assert property (@(sel) !$isunknown(sel))
    else $error("mux_4to1: sel has X/Z");

  // First level correctness
  assert property (@(a or b or sel or ab_sel) (!$isunknown(sel[0])) |-> ##0 (ab_sel === (sel[0] ? b : a)))
    else $error("mux_4to1: ab_sel mismatch");
  assert property (@(c or d or sel or cd_sel) (!$isunknown(sel[0])) |-> ##0 (cd_sel === (sel[0] ? d : c)))
    else $error("mux_4to1: cd_sel mismatch");

  // Second level correctness
  assert property (@(ab_sel or cd_sel or sel or y) (!$isunknown(sel[1])) |-> ##0 (y === (sel[1] ? cd_sel : ab_sel)))
    else $error("mux_4to1: second-level mux mismatch");

  // End-to-end 4:1 equivalence (when select is known)
  assert property (@(a or b or c or d or sel or y)
                   (!$isunknown(sel)) |-> ##0
                   (y === (sel[1] ? (sel[0] ? d : c) : (sel[0] ? b : a))))
    else $error("mux_4to1: y != selected input");

  // Coverage: each select value observed with correct routing
  cover property (@(a or sel or y) (sel===2'b00) && (y===a));
  cover property (@(b or sel or y) (sel===2'b01) && (y===b));
  cover property (@(c or sel or y) (sel===2'b10) && (y===c));
  cover property (@(d or sel or y) (sel===2'b11) && (y===d));

  // Coverage: for each bit, selected input changes propagate to y
  genvar i;
  generate
    for (i=0; i<4; i++) begin : gen_route_cov
      cover property (@(a[i] or sel or y[i]) (sel===2'b00) && $changed(a[i]) ##0 (y[i]===a[i]));
      cover property (@(b[i] or sel or y[i]) (sel===2'b01) && $changed(b[i]) ##0 (y[i]===b[i]));
      cover property (@(c[i] or sel or y[i]) (sel===2'b10) && $changed(c[i]) ##0 (y[i]===c[i]));
      cover property (@(d[i] or sel or y[i]) (sel===2'b11) && $changed(d[i]) ##0 (y[i]===d[i]));
    end
  endgenerate
endmodule

bind mux_4to1 mux_4to1_sva u_mux_4to1_sva (.*);