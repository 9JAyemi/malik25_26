// SVA for mux_2to1
module mux_2to1_sva (input logic A, B, sel, Y);

  default clocking cb @(*) ; endclocking

  // Functional equivalence (4-state accurate)
  assert property (Y === ((~sel & A) | (sel & B)));

  // Truth table when selected data is known
  assert property ((sel === 1'b0 && !$isunknown(A)) |-> (Y === A));
  assert property ((sel === 1'b1 && !$isunknown(B)) |-> (Y === B));

  // Determinism when data inputs are equal (regardless of sel)
  assert property ((A === B && !$isunknown({A,B})) |-> (Y === A));

  // X-propagation sanity
  assert property (($isunknown(sel) && !$isunknown({A,B}) && (A !== B)) |-> $isunknown(Y));
  assert property ((!$isunknown({A,B,sel})) |-> !$isunknown(Y));

  // Coverage
  cover property (sel == 1'b0 && A == 1'b0 && Y == 1'b0);
  cover property (sel == 1'b0 && A == 1'b1 && Y == 1'b1);
  cover property (sel == 1'b1 && B == 1'b0 && Y == 1'b0);
  cover property (sel == 1'b1 && B == 1'b1 && Y == 1'b1);
  cover property ($isunknown(sel) && A === B && !$isunknown({A,B}) && Y === A);
  cover property ($isunknown(sel) && !$isunknown({A,B}) && (A !== B) && $isunknown(Y));

endmodule

bind mux_2to1 mux_2to1_sva sva_inst (.*);