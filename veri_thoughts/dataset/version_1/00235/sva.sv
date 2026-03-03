// SVA checker for four_to_one
module four_to_one_sva (
  input logic A1, A2, B1, B2, X,
  input logic A_low, A_high, B_low, B_high
);
  default clocking cb @(*); endclocking

  // No X/Z on key signals
  a_known:  assert property (!$isunknown({A1,A2,B1,B2,X,A_low,A_high,B_low,B_high}));

  // Internal wire definitions
  a_low_def:   assert property (A_low  == ~(A1 | A2));
  a_high_def:  assert property (A_high ==  (A1 & A2));
  b_low_def:   assert property (B_low  == ~(B1 | B2));
  b_high_def:  assert property (B_high ==  (B1 & B2));

  // Mutual exclusion of low/high detects
  a_mutex: assert property (!(A_low  && A_high));
  b_mutex: assert property (!(B_low  && B_high));

  // Uniformity relations
  a_uniform: assert property ((A_low || A_high) == ~(A1 ^ A2));
  b_uniform: assert property ((B_low || B_high) == ~(B1 ^ B2));

  // Output function equivalence (both internal-wire and input-only forms)
  x_func_wires: assert property (X == ((A_low & B_low) | (A_high & B_high)));
  x_func_inputs: assert property (X == (~(A1 ^ A2) & ~(B1 ^ B2) & ~(A1 ^ B1)));

  // Strong implications for key cases
  x_when_both_low:  assert property ((A_low  && B_low)  |-> X);
  x_when_both_high: assert property ((A_high && B_high) |-> X);
  x_when_mixed:     assert property (((A_low && B_high) || (A_high && B_low)) |-> !X);

  // Minimal output stability: if inputs stable, X stable
  x_stable: assert property ($stable({A1,A2,B1,B2}) |-> $stable(X));

  // Coverage
  cover_X1: cover property (X);
  cover_X0: cover property (!X);
  cover_X_r: cover property (@(posedge X) 1'b1);
  cover_X_f: cover property (@(negedge X) 1'b1);

  // Cover all 16 input combinations
  generate
    for (genvar i = 0; i < 16; i++) begin : CMB
      localparam logic [3:0] V = i[3:0];
      cover_all_inputs: cover property ({A1,A2,B1,B2} == V);
    end
  endgenerate
endmodule

// Bind into DUT (connects to internals by name)
bind four_to_one four_to_one_sva four_to_one_sva_i (.*)