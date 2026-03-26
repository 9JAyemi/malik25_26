// RTL is combinational with no native clock or reset; assertions are sampled on clk.
module adder4_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic       C_out
);

    // The outputs must match the full 5-bit sum of A and B.
    check_full_add_result: assert property (
        @(posedge clk) {C_out, S} == ({1'b0, A} + {1'b0, B})
    );

    // The sum bus must match the low 4 bits of A plus B.
    check_sum_bits: assert property (
        @(posedge clk) S == (A + B)
    );

    // The least-significant sum bit has no carry-in and must be A[0] xor B[0].
    check_lsb_xor: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0])
    );

    // The low 3 sum bits must match the low 3 bits of the partial addition.
    check_low_three_sum: assert property (
        @(posedge clk) S[2:0] == (A[2:0] + B[2:0])
    );

    // Adding zero on A must pass B through with no carry-out.
    check_zero_a_passthrough: assert property (
        @(posedge clk) (A == 4'h0) |-> ({C_out, S} == {1'b0, B})
    );

    // Adding zero on B must pass A through with no carry-out.
    check_zero_b_passthrough: assert property (
        @(posedge clk) (B == 4'h0) |-> ({C_out, S} == {1'b0, A})
    );

    // Carry-out must be low when the sum is less than 16.
    check_no_carry_when_sum_fits: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B}) < 5'd16) |-> (C_out == 1'b0)
    );

    // Carry-out must be high when the sum is 16 or greater.
    check_carry_when_sum_overflows: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B}) >= 5'd16) |-> (C_out == 1'b1)
    );

    // The maximum input pair must produce 0x1E.
    check_max_plus_max: assert property (
        @(posedge clk) ((A == 4'hF) && (B == 4'hF)) |-> ((S == 4'hE) && (C_out == 1'b1))
    );

    // Adding 0xF and 0x1 must wrap the sum and assert carry-out.
    check_f_plus_one_wrap: assert property (
        @(posedge clk) (((A == 4'hF) && (B == 4'h1)) || ((A == 4'h1) && (B == 4'hF)))
            |-> ((S == 4'h0) && (C_out == 1'b1))
    );

endmodule