module four_bit_adder_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic CIN,
  input logic [3:0] SUM,
  input logic COUT,
  input logic VPWR,
  input logic VGND
);
  // No clock or reset in RTL; combinational logic; assertions use posedge $global_clock with no reset disable.
  // Key behavior: 4-bit ripple-carry addition: {COUT,SUM} == A + B + CIN; VPWR/VGND are unused.

  // SUM and COUT must equal the 5-bit addition of A, B, and CIN.
  check_addition_packed: assert property (
    @(posedge $global_clock) {COUT, SUM} == ({1'b0, A} + {1'b0, B} + CIN)
  );

  // SUM must match the low 4 bits of A + B + CIN.
  check_sum_lowbits: assert property (
    @(posedge $global_clock) SUM == (({1'b0, A} + {1'b0, B} + CIN)[3:0])
  );

  // COUT must match the carry-out bit (bit 4) of A + B + CIN.
  check_cout_bit: assert property (
    @(posedge $global_clock) COUT == (({1'b0, A} + {1'b0, B} + CIN)[4])
  );

  // LSB sum bit equals XOR of A[0], B[0], and CIN.
  check_sum_bit0_xor: assert property (
    @(posedge $global_clock) SUM[0] == (A[0] ^ B[0] ^ CIN)
  );

  // SUM[1] equals XOR of A[1], B[1], and carry from bit 0.
  check_sum_bit1_xor_with_c0: assert property (
    @(posedge $global_clock)
      SUM[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN)))
  );

  // Outputs remain stable if A, B, and CIN are stable (no hidden state or VPWR/VGND dependence).
  check_outputs_stable_on_stable_inputs: assert property (
    @(posedge $global_clock) ($stable(A) && $stable(B) && $stable(CIN)) |-> ($stable(SUM) && $stable(COUT))
  );

  // Adding zeros yields zero result and no carry.
  check_zero_case: assert property (
    @(posedge $global_clock) (A == 4'd0 && B == 4'd0 && CIN == 1'b0) |-> (SUM == 4'd0 && COUT == 1'b0)
  );

  // 0xF + 0xF + 1 yields SUM=0xF and COUT=1.
  check_max_plus_one: assert property (
    @(posedge $global_clock) (A == 4'hF && B == 4'hF && CIN == 1'b1) |-> (SUM == 4'hF && COUT == 1'b1)
  );

endmodule