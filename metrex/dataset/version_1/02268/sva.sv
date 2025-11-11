// SVA for nand4 — concise, high-quality checks and coverage

module nand4_sva (
  input logic a, b, c, d,
  input logic y,
  input logic temp
);

  // Functional correctness (delta-cycle safe)
  assert property (@(a or b or c or d) 1 |-> ##0 (y === ~(a & b & c & d)));

  // Internal signal consistency
  assert property (@(a or b or c or d or temp) 1 |-> ##0 (temp === (a & b & c & d) && y === ~temp));

  // X/Z behavior: clean in -> clean out; unknown in -> unknown out
  assert property (@(a or b or c or d) !$isunknown({a,b,c,d}) |-> ##0 !$isunknown(y));
  assert property (@(a or b or c or d)  $isunknown({a,b,c,d}) |-> ##0  $isunknown(y));

  // No glitches: y cannot change unless inputs change
  assert property (@(a or b or c or d or y) $stable({a,b,c,d}) |-> ##0 $stable(y));

  // Output implies correct input pattern (redundant with func check, but strong and localizes failures)
  assert property (@(a or b or c or d or y) 1 |-> ##0 ((y === 1'b0) -> (a & b & c & d)));
  assert property (@(a or b or c or d or y) 1 |-> ##0 ((y === 1'b1) -> ~(a & b & c & d)));

  // Basic functional coverage
  cover property (@(a or b or c or d) ##0 (y === 1'b0));
  cover property (@(a or b or c or d) ##0 (y === 1'b1));
  cover property (@(y) ##0 $rose(y));
  cover property (@(y) ##0 $fell(y));

  // Exhaustive input minterm coverage (all 16 combinations)
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : minterm_cov
      localparam logic [3:0] V = i[3:0];
      cover property (@(a or b or c or d) ##0 ({a,b,c,d} === V));
    end
  endgenerate

endmodule

// Bind into DUT to access internal 'temp'
bind nand4 nand4_sva sva_nand4 (.*);