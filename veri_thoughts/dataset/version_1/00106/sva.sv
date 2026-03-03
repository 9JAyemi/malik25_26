// SVA checker for sky130_fd_sc_lp__a22o (X = (A1 & A2) | (B1 & B2))
module sky130_fd_sc_lp__a22o_sva (
  input logic A1, A2, B1, B2, X,
  // bind these to internals for structural checks
  input logic and0_out, and1_out, or0_out_X
);

  logic comb_expr;
  assign comb_expr = (A1 & A2) | (B1 & B2);

  // Functional equivalence after delta-cycle settle on any input change
  property func_equiv_settle;
    @(*) $changed({A1,A2,B1,B2}) |-> ##0 (X === comb_expr);
  endproperty
  assert property (func_equiv_settle);

  // If inputs are known, X must be known and match the boolean function
  property func_no_x_when_inputs_known;
    @(*) !$isunknown({A1,A2,B1,B2}) |-> ##0 (! $isunknown(X) && (X == comb_expr));
  endproperty
  assert property (func_no_x_when_inputs_known);

  // Structural checks (AND/OR/BUF) after settle
  property and0_check;
    @(*) $changed({B1,B2}) |-> ##0 (and0_out === (B1 & B2));
  endproperty
  assert property (and0_check);

  property and1_check;
    @(*) $changed({A1,A2}) |-> ##0 (and1_out === (A1 & A2));
  endproperty
  assert property (and1_check);

  property or_check;
    @(*) $changed({and1_out,and0_out}) |-> ##0 (or0_out_X === (and1_out | and0_out));
  endproperty
  assert property (or_check);

  property buf_check;
    @(*) $changed(or0_out_X) |-> ##0 (X === or0_out_X);
  endproperty
  assert property (buf_check);

  // Functional coverage (concise but complete for all logical cases)
  cover property (@(*) !$isunknown({A1,A2,B1,B2}) && (comb_expr == 1'b0)); // X=0
  cover property (@(*) !$isunknown({A1,A2,B1,B2}) && (comb_expr == 1'b1)); // X=1

  // Path-specific activations
  cover property (@(*) !$isunknown({A1,A2,B1,B2}) && ((A1 & A2) && !(B1 & B2))); // A-path only
  cover property (@(*) !$isunknown({A1,A2,B1,B2}) && (!(A1 & A2) && (B1 & B2))); // B-path only
  cover property (@(*) !$isunknown({A1,A2,B1,B2}) && ((A1 & A2) &&  (B1 & B2))); // both paths
  cover property (@(*) !$isunknown({A1,A2,B1,B2}) && (!(A1 & A2) && !(B1 & B2))); // neither path

endmodule

// Example bind (connect internals for structural checks)
bind sky130_fd_sc_lp__a22o sky130_fd_sc_lp__a22o_sva u_a22o_sva (
  .A1(A1), .A2(A2), .B1(B1), .B2(B2), .X(X),
  .and0_out(and0_out), .and1_out(and1_out), .or0_out_X(or0_out_X)
);