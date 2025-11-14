// SVA for two_bit_comparator: Y must equal (A >= B) for all 2’b known inputs.
// Bind this file to the DUT; concise, covers all functional branches.

module two_bit_comparator_sva (
  input logic [1:0] A,
  input logic [1:0] B,
  input logic       Y
);

  // No X/Z on inputs/outputs after combinational settle
  assert property (@(A or B or Y) ##0 !$isunknown({A,B,Y}))
    else $error("X/Z detected on A/B/Y");

  // Golden functional check (unsigned compare)
  assert property (@(A or B) (!$isunknown({A,B})) |-> ##0 (Y == (A >= B)))
    else $error("Y != (A >= B)");

  // Functional branch coverage (exercise all code paths)
  cover property (@(A or B) ##0 (!$isunknown({A,B}) && (A[1]==B[1]) && (A[0]>=B[0]) &&  Y)); // msb equal, lsb >=
  cover property (@(A or B) ##0 (!$isunknown({A,B}) && (A[1]==B[1]) && (A[0]< B[0]) && !Y)); // msb equal, lsb <
  cover property (@(A or B) ##0 (!$isunknown({A,B}) && (A[1]> B[1])                 &&  Y)); // msb >
  cover property (@(A or B) ##0 (!$isunknown({A,B}) && (A[1]< B[1])                 && !Y)); // msb <

  // Optional: observe Y toggles (sanity coverage)
  cover property (@(A or B) ##0 $rose(Y));
  cover property (@(A or B) ##0 $fell(Y));

endmodule

bind two_bit_comparator two_bit_comparator_sva u_two_bit_comparator_sva (.A(A), .B(B), .Y(Y));