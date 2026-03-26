module binary_adder_sva (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic [3:0]  S,
    input logic        C_out
);

    // Full output matches the 5-bit sum of A and B.
    check_full_sum_match: assert property (
        @(posedge clk) {C_out, S} == ({1'b0, A} + {1'b0, B})
    );

    // Sum output matches the low 4 bits of the addition.
    check_sum_bits_match: assert property (
        @(posedge clk) S == ({1'b0, A} + {1'b0, B})[3:0]
    );

    // Carry output matches the high bit of the addition.
    check_carry_out_match: assert property (
        @(posedge clk) C_out == ({1'b0, A} + {1'b0, B})[4]
    );

    // Zero on A passes B through with no carry.
    check_a_zero_passthrough: assert property (
        @(posedge clk) (A == 4'h0) |-> ({C_out, S} == {1'b0, B})
    );

    // Zero on B passes A through with no carry.
    check_b_zero_passthrough: assert property (
        @(posedge clk) (B == 4'h0) |-> ({C_out, S} == {1'b0, A})
    );

    // Max plus max produces 0xE with carry asserted.
    check_max_plus_max: assert property (
        @(posedge clk) ((A == 4'hF) && (B == 4'hF)) |-> ((S == 4'hE) && (C_out == 1'b1))
    );

endmodule