// SVA for ripple_carry_adder
module rca_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       C_in,
  input  logic       CLK,
  input  logic [3:0] S,
  input  logic       C_out,
  input  logic [3:0] sum,
  input  logic [3:0] carry
);
  default clocking cb @ (posedge CLK); endclocking

  // End-to-end correctness (zero-extend to 5 bits)
  a_end_to_end: assert property ({C_out,S} == ({1'b0,A} + {1'b0,B} + C_in));

  // Structural consistency
  a_s_eq_sum: assert property (S == sum);

  // Stage-by-stage full-adder equations
  a_s0:    assert property (sum[0] == (A[0]^B[0]^C_in));
  a_c0:    assert property (carry[0] == ((A[0]&B[0]) | (A[0]&C_in) | (B[0]&C_in)));

  a_s1:    assert property (sum[1] == (A[1]^B[1]^carry[0]));
  a_c1:    assert property (carry[1] == ((A[1]&B[1]) | (A[1]&carry[0]) | (B[1]&carry[0])));

  a_s2:    assert property (sum[2] == (A[2]^B[2]^carry[1]));
  a_c2:    assert property (carry[2] == ((A[2]&B[2]) | (A[2]&carry[1]) | (B[2]&carry[1])));

  a_s3:    assert property (sum[3] == (A[3]^B[3]^carry[2]));
  a_cout:  assert property (C_out     == ((A[3]&B[3]) | (A[3]&carry[2]) | (B[3]&carry[2])));

  // X-safety on outputs when inputs are known
  a_no_x_out: assert property (!$isunknown({A,B,C_in})) |-> (!$isunknown({S,C_out}));

  // Concise coverage
  c_zero:            cover property ({C_out,S} == 5'd0);
  c_max:             cover property ({C_out,S} == 5'd31);
  c_propagate_chain: cover property (C_in && ((A^B)==4'hF) && C_out);
  c_full_ripple:     cover property (carry[0] && carry[1] && carry[2] && C_out);
endmodule

// Bind into DUT (accesses internal sum/carry)
bind ripple_carry_adder rca_sva rca_sva_i (.*);