// SVA checker for sky130_fd_sc_hd__and3b (bindable, port-only)
module sky130_fd_sc_hd__and3b_sva (
  input logic A_N,
  input logic B,
  input logic C,
  input logic X
);
  logic expected;
  assign expected = B & C & ~A_N;

  // Functional equivalence (4-state)
  assert property (@(A_N or B or C or X) X === expected);

  // Controlling values and key corner cases
  assert property (@(A_N or B or C) (B == 1'b0) |-> (X == 1'b0));
  assert property (@(A_N or B or C) (C == 1'b0) |-> (X == 1'b0));
  assert property (@(A_N or B or C) (B && C && !A_N) |-> (X == 1'b1));
  assert property (@(A_N or B or C) (B && C &&  A_N) |-> (X == 1'b0));

  // No X/Z on output when inputs are known
  assert property (@(A_N or B or C) (!$isunknown({A_N,B,C})) |-> (!$isunknown(X)));

  // Toggle coverage
  cover property (@(A_N or B or C or X) $rose(X));
  cover property (@(A_N or B or C or X) $fell(X));

  // Input space coverage (all 8 combinations with known inputs)
  cover property (@(A_N or B or C) (!$isunknown({A_N,B,C}) && {A_N,B,C} == 3'b000));
  cover property (@(A_N or B or C) (!$isunknown({A_N,B,C}) && {A_N,B,C} == 3'b001));
  cover property (@(A_N or B or C) (!$isunknown({A_N,B,C}) && {A_N,B,C} == 3'b010));
  cover property (@(A_N or B or C) (!$isunknown({A_N,B,C}) && {A_N,B,C} == 3'b011));
  cover property (@(A_N or B or C) (!$isunknown({A_N,B,C}) && {A_N,B,C} == 3'b100));
  cover property (@(A_N or B or C) (!$isunknown({A_N,B,C}) && {A_N,B,C} == 3'b101));
  cover property (@(A_N or B or C) (!$isunknown({A_N,B,C}) && {A_N,B,C} == 3'b110));
  cover property (@(A_N or B or C) (!$isunknown({A_N,B,C}) && {A_N,B,C} == 3'b111));

  // Functional 1-coverage
  cover property (@(A_N or B or C) (B && C && !A_N && X));
endmodule

bind sky130_fd_sc_hd__and3b sky130_fd_sc_hd__and3b_sva u_and3b_sva (.A_N(A_N), .B(B), .C(C), .X(X));


// Optional: place inside the DUT to directly check internal nets
// (uncomment inside sky130_fd_sc_hd__and3b if internal net checks are desired)
/*
  // not stage
  assert property (@(A_N) not0_out === ~A_N);
  // and stage
  assert property (@(A_N or B or C) and0_out_X === (C & not0_out & B));
  // buf stage
  assert property (@(and0_out_X or X) X === and0_out_X);
*/