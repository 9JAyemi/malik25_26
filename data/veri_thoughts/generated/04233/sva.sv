module four_bit_adder_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic       C_out
);

    // Overall 5-bit result must equal the sum of A and B.
    check_total_sum: assert property (
        @(posedge clk) {C_out, S} == ({1'b0, A} + {1'b0, B})
    );

    // The LSB sum is the XOR of A[0] and B[0] because Cin is tied low.
    check_lsb_sum: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0])
    );

    // Zero plus zero must produce zero with no carry.
    check_zero_plus_zero: assert property (
        @(posedge clk) ((A == 4'h0) && (B == 4'h0)) |-> ({C_out, S} == 5'h00)
    );

    // Adding zero on A must pass B through with no carry.
    check_add_zero_on_a: assert property (
        @(posedge clk) (A == 4'h0) |-> ((S == B) && (C_out == 1'b0))
    );

    // Adding zero on B must pass A through with no carry.
    check_add_zero_on_b: assert property (
        @(posedge clk) (B == 4'h0) |-> ((S == A) && (C_out == 1'b0))
    );

    // Carry-out must assert when the 5-bit sum exceeds 4 bits.
    check_carry_on_overflow: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B}) >= 5'd16) |-> (C_out == 1'b1)
    );

    // Carry-out must remain low when the 5-bit sum fits in 4 bits.
    check_no_carry_without_overflow: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B}) < 5'd16) |-> (C_out == 1'b0)
    );

    // The maximum input case must produce 0xE with carry-out set.
    check_max_plus_max: assert property (
        @(posedge clk) ((A == 4'hF) && (B == 4'hF)) |-> ((S == 4'hE) && (C_out == 1'b1))
    );

    // Complementary operands must sum to 0xF with no carry.
    check_complementary_operands: assert property (
        @(posedge clk) (B == ~A) |-> ((S == 4'hF) && (C_out == 1'b0))
    );

endmodule