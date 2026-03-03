// SVA checker for sky130_fd_sc_ms__a32o
module sky130_fd_sc_ms__a32o_sva (
  input logic A1, A2, A3, B1, B2,
  input logic X,
  input logic and0_out, and1_out, or0_out_X
);

  // Derived terms
  logic a_term, b_term, expr;
  always_comb begin
    a_term = A1 & A2 & A3;
    b_term = B1 & B2;
    expr   = a_term | b_term;
  end

  // Immediate combinational correctness (localizes bugs)
  always_comb begin
    assert (and0_out  === a_term)             else $error("a32o and0_out != A1&A2&A3");
    assert (and1_out  === b_term)             else $error("a32o and1_out != B1&B2");
    assert (or0_out_X === (and0_out|and1_out))else $error("a32o or0_out_X != and0_out|and1_out");
    assert (X         === expr)               else $error("a32o X != (A1&A2&A3)|(B1&B2)");
  end

  // Settle in same timestep on any driving change
  property settle_comb;
    @(A1 or A2 or A3 or B1 or B2 or and0_out or and1_out or or0_out_X or X)
      ##0 (X === expr);
  endproperty
  assert property (settle_comb);

  // No spurious output changes without input change
  property x_changes_only_if_inputs_change;
    @(X) $changed(X) |-> $changed({A1,A2,A3,B1,B2});
  endproperty
  assert property (x_changes_only_if_inputs_change);

  // If Boolean function does not change, X must stay stable
  property no_glitch_when_expr_stable;
    @(A1 or A2 or A3 or B1 or B2) !$changed(expr) |-> $stable(X);
  endproperty
  assert property (no_glitch_when_expr_stable);

  // No X/Z on X when inputs are known
  property no_x_on_output_when_inputs_known;
    @(*) !$isunknown({A1,A2,A3,B1,B2}) |-> ##0 !$isunknown(X);
  endproperty
  assert property (no_x_on_output_when_inputs_known);

  // Functional coverage
  cover property (@(A1 or A2 or A3 or B1 or B2) ( a_term && !b_term) ##0 (X==1));
  cover property (@(A1 or A2 or A3 or B1 or B2) (!a_term &&  b_term) ##0 (X==1));
  cover property (@(A1 or A2 or A3 or B1 or B2) ( a_term &&  b_term) ##0 (X==1));
  cover property (@(A1 or A2 or A3 or B1 or B2) (!a_term && !b_term) ##0 (X==0));

  // Output edges
  cover property (@(posedge X) 1);
  cover property (@(negedge X) 1);

  // Each input exercises both edges
  cover property (@(posedge A1) 1);
  cover property (@(negedge A1) 1);
  cover property (@(posedge A2) 1);
  cover property (@(negedge A2) 1);
  cover property (@(posedge A3) 1);
  cover property (@(negedge A3) 1);
  cover property (@(posedge B1) 1);
  cover property (@(negedge B1) 1);
  cover property (@(posedge B2) 1);
  cover property (@(negedge B2) 1);

endmodule

// Bind into the DUT
bind sky130_fd_sc_ms__a32o sky130_fd_sc_ms__a32o_sva u_sky130_fd_sc_ms__a32o_sva (.*);