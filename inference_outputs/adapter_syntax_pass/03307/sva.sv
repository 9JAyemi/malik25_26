module adder_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] S,
    input logic       C_out
);

    // S is the low 8 bits of A plus B.
    check_sum_low_bits: assert property (
        @($global_clock) S == (A + B)
    );

    // C_out is the carry bit from the 8-bit addition.
    check_carry_out: assert property (
        @($global_clock) C_out == (({1'b0, A} + {1'b0, B}) >= 9'h100)
    );

    // The concatenated result matches the 9-bit sum.
    check_concatenated_result: assert property (
        @($global_clock) {C_out, S} == ({1'b0, A} + {1'b0, B})
    );

    // Zero on A passes B through with no carry.
    check_zero_a_passthrough: assert property (
        @($global_clock) (A == 8'h00) |-> ((S == B) && (C_out == 1'b0))
    );

    // Zero on B passes A through with no carry.
    check_zero_b_passthrough: assert property (
        @($global_clock) (B == 8'h00) |-> ((S == A) && (C_out == 1'b0))
    );

    // 8'hFF plus 8'h01 wraps to 8'h00 with carry.
    check_ff_plus_one_wrap: assert property (
        @($global_clock) ((A == 8'hFF) && (B == 8'h01)) |-> ((S == 8'h00) && (C_out == 1'b1))
    );

endmodule