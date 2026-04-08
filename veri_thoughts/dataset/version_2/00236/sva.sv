module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] OUT,
    input logic CARRY_OUT,
    input logic CARRY_IN
);

    // Combined outputs equal the 5-bit addition result.
    check_total_sum: assert property (
        @($global_clock) {CARRY_OUT, OUT} == ({1'b0, A} + {1'b0, B} + CARRY_IN)
    );

    // Bit 0 matches full-adder XOR behavior.
    check_lsb_sum: assert property (
        @($global_clock) OUT[0] == (A[0] ^ B[0] ^ CARRY_IN)
    );

    // With no carry-in, the module reduces to A plus B.
    check_no_carry_in_add: assert property (
        @($global_clock) (CARRY_IN == 1'b0) |-> ({CARRY_OUT, OUT} == ({1'b0, A} + {1'b0, B}))
    );

    // A equal to zero passes B through with carry-in addition.
    check_zero_a_passthrough: assert property (
        @($global_clock) (A == 4'b0000) |-> ({CARRY_OUT, OUT} == ({1'b0, B} + CARRY_IN))
    );

    // B equal to zero passes A through with carry-in addition.
    check_zero_b_passthrough: assert property (
        @($global_clock) (B == 4'b0000) |-> ({CARRY_OUT, OUT} == ({1'b0, A} + CARRY_IN))
    );

    // Zero operands produce only the carry-in in the LSB.
    check_zero_operands: assert property (
        @($global_clock) ((A == 4'b0000) && (B == 4'b0000)) |-> ({CARRY_OUT, OUT} == {4'b0000, CARRY_IN})
    );

    // Carry-out is high exactly when the 4-bit addition overflows.
    check_carry_out_overflow: assert property (
        @($global_clock) CARRY_OUT == (({1'b0, A} + {1'b0, B} + CARRY_IN) > 5'd15)
    );

    // Adding one to 4'hF wraps OUT to zero and raises carry-out.
    check_increment_overflow: assert property (
        @($global_clock) ((A == 4'hF) && (B == 4'h0) && (CARRY_IN == 1'b1)) |-> ({CARRY_OUT, OUT} == 5'h10)
    );

    // Maximum inputs produce all ones on the 5-bit result.
    check_max_input_sum: assert property (
        @($global_clock) ((A == 4'hF) && (B == 4'hF) && (CARRY_IN == 1'b1)) |-> ({CARRY_OUT, OUT} == 5'h1F)
    );

endmodule