// SVA checker for shift_left_2
module shift_left_2_sva (
  input  logic       clk,
  input  logic [3:0] A,
  input  logic [3:0] X
);
  default clocking cb @(posedge clk); endclocking

  // Functional equivalence (when inputs are known)
  a_func: assert property (!$isunknown(A) |-> (X == {A[1:0], 2'b00} && !$isunknown(X)));

  // Bit-level constraints (redundant but pinpoint failures)
  a_low_zero: assert property (X[1:0] == 2'b00);
  a_map3:     assert property (X[3] == A[1]);
  a_map2:     assert property (X[2] == A[0]);

  // Independence: upper input bits must not affect output
  a_upper_indep: assert property ($stable(A[1:0]) && $changed(A[3:2]) |-> $stable(X));

  // Toggle coupling: changes in A[1:0] reflect on X[3:2]
  a_tog3: assert property ($changed(A[1]) |-> $changed(X[3]));
  a_tog2: assert property ($changed(A[0]) |-> $changed(X[2]));

  // Functional coverage: exercise all result classes
  c_00: cover property (A[1:0]==2'b00 && X==4'b0000);
  c_01: cover property (A[1:0]==2'b01 && X==4'b0100);
  c_10: cover property (A[1:0]==2'b10 && X==4'b1000);
  c_11: cover property (A[1:0]==2'b11 && X==4'b1100);
endmodule

// Example bind (hook clk to any free-running TB clock):
// bind shift_left_2 shift_left_2_sva u_shift_left_2_sva (.clk(tb_clk), .A(A), .X(X));