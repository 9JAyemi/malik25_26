// SVA for mux_2to1. Bind this file to the DUT.

module mux_2to1_sva (
  input logic Y,
  input logic A,
  input logic B,
  input logic S
);

  // Functional correctness
  ap_sel0: assert property (@(*) (S === 1'b0) |-> (Y === A));
  ap_sel1: assert property (@(*) (S === 1'b1) |-> (Y === B));
  ap_equal_inputs: assert property (@(*) (A === B) |-> (Y === A)); // regardless of S

  // Knownness: if all inputs are known, output must be known
  ap_known_out: assert property (@(*) (!$isunknown({A,B,S})) |-> !$isunknown(Y));

  // Optional: flag unknown select (helps catch X-prop on Y)
  ap_sel_known: assert property (@(*) !$isunknown(S))
    else $warning("mux_2to1: Select S is X/Z; Y may be X.");

  // Coverage: exercise both legs and values
  cp_takeA0: cover property (@(*) (S==1'b0 && A==1'b0 && Y==1'b0));
  cp_takeA1: cover property (@(*) (S==1'b0 && A==1'b1 && Y==1'b1));
  cp_takeB0: cover property (@(*) (S==1'b1 && B==1'b0 && Y==1'b0));
  cp_takeB1: cover property (@(*) (S==1'b1 && B==1'b1 && Y==1'b1));

  // Coverage: select toggles with differing inputs, Y follows the selected input
  cp_sel_up_diff:   cover property (@(posedge S) (A^B) ##0 (Y === B));
  cp_sel_down_diff: cover property (@(negedge S) (A^B) ##0 (Y === A));

  // Coverage: select toggles with equal inputs, Y stays the same
  cp_sel_toggle_same: cover property (@(posedge S or negedge S) (A===B) ##0 (Y===A));

endmodule

bind mux_2to1 mux_2to1_sva u_mux_2to1_sva (.Y(Y), .A(A), .B(B), .S(S));