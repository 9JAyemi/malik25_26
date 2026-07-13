module ripple_carry_adder_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic       carry_in,
  input logic [3:0] sum,
  input logic       carry_out
);
  // Combinational DUT with no clock/reset; assertions use $global_clock.

  // Local expected propagate/generate and carry chain computed from DUT inputs.
  wire [3:0] p = A ^ B;
  wire [3:0] g = A & B;

  wire [3:0] c;
  assign c[0] = carry_in;
  assign c[1] = g[0] | (p[0] & c[0]);
  assign c[2] = g[1] | (p[1] & c[1]);
  assign c[3] = g[2] | (p[2] & c[2]);

  wire       c4 = g[3] | (p[3] & c[3]);
  wire [4:0] expected = {1'b0, A} + {1'b0, B} + carry_in;

  // Sum+carry equals arithmetic addition of operands and carry_in.
  check_add_packed: assert property (
    @(posedge $global_clock) {carry_out, sum} == expected
  );

  // Bit 0 sum is XOR of A[0], B[0], and carry_in.
  sum_bit0_eq: assert property (
    @(posedge $global_clock) sum[0] == (p[0] ^ c[0])
  );

  // Bit 1 sum is XOR of A[1]^B[1] with carry into bit 1.
  sum_bit1_eq: assert property (
    @(posedge $global_clock) sum[1] == (p[1] ^ c[1])
  );

  // Bit 2 sum is XOR of A[2]^B[2] with carry into bit 2.
  sum_bit2_eq: assert property (
    @(posedge $global_clock) sum[2] == (p[2] ^ c[2])
  );

  // Bit 3 sum is XOR of A[3]^B[3] with carry into bit 3.
  sum_bit3_eq: assert property (
    @(posedge $global_clock) sum[3] == (p[3] ^ c[3])
  );

  // Carry-out equals ripple chain carry from bit 3.
  carry_out_eq_chain: assert property (
    @(posedge $global_clock) carry_out == c4
  );

  // Sum equals propagate XOR carry vector.
  sum_vector_eq: assert property (
    @(posedge $global_clock) sum == (p ^ {c[3], c[2], c[1], c[0]})
  );

  // Carry-out equals overflow bit of the arithmetic result.
  carry_out_matches_overflow: assert property (
    @(posedge $global_clock) carry_out == expected[4]
  );

  // If inputs are stable across a cycle, outputs are stable.
  outputs_stable_when_inputs_stable: assert property (
    @(posedge $global_clock) $stable({A, B, carry_in}) |-> $stable({sum, carry_out})
  );

  // Known inputs imply known outputs.
  outputs_known_when_inputs_known: assert property (
    @(posedge $global_clock) !$isunknown({A, B, carry_in}) |-> !$isunknown({sum, carry_out})
  );

  // Adding zero (B=0, carry_in=0) returns A with no carry.
  add_zero_identity: assert property (
    @(posedge $global_clock) (B == 4'b0000) && (carry_in == 1'b0) |-> (sum == A) && (carry_out == 1'b0)
  );
endmodule