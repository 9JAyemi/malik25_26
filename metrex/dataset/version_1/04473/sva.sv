// SVA for greater_than_or_equal
// Bind into the DUT
bind greater_than_or_equal greater_than_or_equal_sva sva_i (.a(a), .b(b), .y(y));

module greater_than_or_equal_sva (input logic [7:0] a, b, input logic y);

  // Functional correctness when inputs are known
  assert property (@(a or b or y) (!$isunknown({a,b})) |-> (y === (a >= b)));

  // Deterministic behavior on unknown inputs (matches Verilog if semantics)
  assert property (@(a or b or y) ($isunknown({a,b})) |-> (y === 1'b0));

  // Output must never be X/Z
  assert property (@(a or b or y) ! $isunknown(y));

  // Output changes only when inputs change (combinational consistency)
  assert property (@(a or b or y) $changed(y) |-> ($changed(a) || $changed(b)));

  // Coverage: equality boundary, gt, lt, and extremes
  cover property (@(a or b or y) (!$isunknown({a,b}) && (a == b) && y));
  cover property (@(a or b or y) (!$isunknown({a,b}) && (a >  b) && y));
  cover property (@(a or b or y) (!$isunknown({a,b}) && (a <  b) && !y));
  cover property (@(a or b or y) (a == 8'h00 && b == 8'hFF && !y));
  cover property (@(a or b or y) (a == 8'hFF && b == 8'h00 && y));

endmodule