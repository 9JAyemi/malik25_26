module four_bit_adder_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic       Cout
);

    // The 5-bit output must equal the arithmetic sum of A and B.
    check_full_sum_match: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B})
    );

    // The least-significant sum bit has no carry-in and is just A[0] xor B[0].
    check_lsb_has_no_carry_in: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0])
    );

    // Adding zero on B must pass A through with no carry-out.
    check_b_zero_passthrough: assert property (
        @(posedge clk) (B == 4'b0000) |-> ({Cout, S} == {1'b0, A})
    );

    // Adding zero on A must pass B through with no carry-out.
    check_a_zero_passthrough: assert property (
        @(posedge clk) (A == 4'b0000) |-> ({Cout, S} == {1'b0, B})
    );

    // If both operands are less than 8, the 4-bit adder cannot overflow.
    check_no_carry_when_msb_clear: assert property (
        @(posedge clk) (!A[3] && !B[3]) |-> (Cout == 1'b0)
    );

    // The maximum input pair must produce 30 decimal as 1_1110.
    check_max_operands_result: assert property (
        @(posedge clk) ((A == 4'hF) && (B == 4'hF)) |-> ({Cout, S} == 5'h1E)
    );

    // Adding 1 to 15 must roll over the sum and assert carry-out.
    check_rollover_on_ff_plus_one: assert property (
        @(posedge clk) (((A == 4'hF) && (B == 4'h1)) || ((A == 4'h1) && (B == 4'hF))) |-> ({Cout, S} == 5'h10)
    );

endmodule