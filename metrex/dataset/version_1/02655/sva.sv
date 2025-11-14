// SVA checker for mod_operator
module mod_operator_sva (
  input logic [31:0] A,
  input logic [31:0] B,
  input logic [31:0] result
);
  default clocking cb @(*); endclocking

  // No-X on output when inputs are known
  a_no_x: assert property (disable iff ($isunknown({A,B})) !$isunknown(result));

  // B == 0 => result == 0
  a_div0:  assert property (disable iff ($isunknown({A,B}))
                            (B == 32'd0) |-> (result == 32'd0));

  // Functional correctness for B != 0
  a_mod:   assert property (disable iff ($isunknown({A,B}))
                            (B != 32'd0) |->
                              (result == (A % B)) &&
                              (result == (A - (A / B) * B)) &&
                              (result < B) &&
                              (result <= A));

  // Explicit passthrough when A < B and B != 0
  a_passthru: assert property (disable iff ($isunknown({A,B}))
                               (B != 32'd0 && A < B) |-> (result == A));

  // Coverage
  c_div0:       cover property (B == 32'd0);
  c_a_lt_b:     cover property (B != 32'd0 && A < B);
  c_a_eq_b:     cover property (B != 32'd0 && A == B);
  c_mult_of_b:  cover property (B != 32'd0 && A > B && (A % B) == 32'd0);
  c_b_is_one:   cover property (B == 32'd1);
endmodule

// Bind into DUT
bind mod_operator mod_operator_sva u_mod_operator_sva (.A(A), .B(B), .result(result));