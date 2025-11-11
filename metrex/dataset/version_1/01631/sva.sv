// SVA checker bound into the DUT. Focused, high-quality assertions + essential coverage.

module adder_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic [3:0] C,
  input  logic       CO,
  input  logic [4:0] sum
);
  default clocking cb @(*) ; endclocking

  // X-propagation control: when inputs are known, outputs and internal sum must be known
  a_no_x_when_inputs_known: assert property (!$isunknown({A,B}) |-> !$isunknown({C,CO,sum}));

  // Direct functional correctness: full 5-bit addition
  a_full_sum_correct:       assert property (!$isunknown({A,B}) |-> {CO,C} == A + B);

  // Internal consistency: sum computed correctly and outputs are proper slices
  a_internal_mapping:       assert property (!$isunknown({A,B}) |-> (sum == A + B && C == sum[3:0] && CO == sum[4]));

  // Essential coverage
  c_no_carry:  cover property (!$isunknown({A,B}) && (CO == 1'b0));
  c_carry:     cover property (!$isunknown({A,B}) && (CO == 1'b1));

  c_zero_zero: cover property (A==4'd0  && B==4'd0  && {CO,C}==5'd0);
  c_max_zero:  cover property (A==4'd15 && B==4'd0  && {CO,C}==5'd15);
  c_zero_max:  cover property (A==4'd0  && B==4'd15 && {CO,C}==5'd15);
  c_max_max:   cover property (A==4'd15 && B==4'd15 && {CO,C}==5'd30);

  // Each output bit goes high at least once
  genvar i;
  generate
    for (i=0; i<4; i++) begin : g_cov_c_bits
      c_cbit_hi: cover property (C[i]);
    end
  endgenerate
endmodule

bind adder adder_sva u_adder_sva (.A(A), .B(B), .C(C), .CO(CO), .sum(sum));