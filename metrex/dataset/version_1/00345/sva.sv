// SVA for logic_module
module logic_module_sva (
  input logic A1,
  input logic A2,
  input logic B1,
  input logic C1,
  input logic X,
  input logic or0_out,
  input logic and0_out_X
);

  // Functional equivalence (end-to-end)
  property p_func_equiv;
    @(A1 or A2 or B1 or C1 or X)
      1 |-> ##0 (X === ((A1 | A2) & B1 & C1));
  endproperty
  assert property (p_func_equiv);

  // Structural checks (gate-level)
  assert property (@(A1 or A2 or or0_out)
                   1 |-> ##0 (or0_out === (A1 | A2)));

  assert property (@(or0_out or B1 or C1 or and0_out_X)
                   1 |-> ##0 (and0_out_X === (or0_out & B1 & C1)));

  assert property (@(and0_out_X or X)
                   1 |-> ##0 (X === and0_out_X));

  // Knownness when inputs are known
  assert property (@(A1 or A2 or B1 or C1 or X)
                   !$isunknown({A1,A2,B1,C1}) |-> ##0 !$isunknown(X));

  // Simple implications
  assert property (@(B1 or C1 or X)
                   (!B1 || !C1) |-> ##0 (X === 1'b0));

  assert property (@(A1 or A2 or B1 or C1 or X)
                   (B1 && C1 && (A1 || A2)) |-> ##0 (X === 1'b1));

  // Coverage
  cover property (@(A1 or A2 or B1 or C1 or X)
                  (B1 && C1 && A1 && !A2) ##0 X);

  cover property (@(A1 or A2 or B1 or C1 or X)
                  (B1 && C1 && !A1 && A2) ##0 X);

  cover property (@(A1 or A2 or B1 or C1 or X)
                  (!B1) ##0 (X == 1'b0));

  cover property (@(A1 or A2 or B1 or C1 or X)
                  (!C1) ##0 (X == 1'b0));

  cover property (@(A1 or A2 or B1 or C1 or X)
                  X !== $past(X));

endmodule

bind logic_module logic_module_sva sva_inst(
  .A1(A1),
  .A2(A2),
  .B1(B1),
  .C1(C1),
  .X(X),
  .or0_out(or0_out),
  .and0_out_X(and0_out_X)
);