module adder_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] S,
    input logic C_out
);

    // Combined outputs must equal the 9-bit sum of A and B.
    check_full_sum_matches_outputs: assert property (
        @(posedge clk) ({C_out, S} == ({1'b0, A} + {1'b0, B}))
    );

    // S must be the low 8 bits of the sum.
    check_sum_low_byte_matches: assert property (
        @(posedge clk) (S == (({1'b0, A} + {1'b0, B})[7:0]))
    );

    // C_out must be the carry bit of the sum.
    check_carry_bit_matches: assert property (
        @(posedge clk) (C_out == (({1'b0, A} + {1'b0, B})[8]))
    );

    // Adding zero on B must return A with no carry.
    check_add_zero_on_b: assert property (
        @(posedge clk) (B == 8'h00) |-> ({C_out, S} == {1'b0, A})
    );

    // Adding zero on A must return B with no carry.
    check_add_zero_on_a: assert property (
        @(posedge clk) (A == 8'h00) |-> ({C_out, S} == {1'b0, B})
    );

    // Overflowing the 8-bit range must assert carry.
    check_overflow_sets_carry: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B}) > 9'h0FF) |-> (C_out == 1'b1)
    );

    // Staying within the 8-bit range must clear carry.
    check_no_overflow_clears_carry: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B}) <= 9'h0FF) |-> (C_out == 1'b0)
    );

    // Adding all ones must produce 9'h1FE.
    check_ff_plus_ff: assert property (
        @(posedge clk) ((A == 8'hFF) && (B == 8'hFF)) |-> ({C_out, S} == 9'h1FE)
    );

    // Adding FF and 01 must wrap the sum and assert carry.
    check_ff_plus_one: assert property (
        @(posedge clk) (((A == 8'hFF) && (B == 8'h01)) || ((A == 8'h01) && (B == 8'hFF))) |-> ({C_out, S} == 9'h100)
    );

    // Adding 80 and 80 must produce zero with carry.
    check_80_plus_80: assert property (
        @(posedge clk) ((A == 8'h80) && (B == 8'h80)) |-> ({C_out, S} == 9'h100)
    );

endmodule