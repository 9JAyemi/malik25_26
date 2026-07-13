module four_bit_adder_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] S,
    input logic       Cout
);

    // Outputs form the 5-bit sum of A, B, and Cin.
    check_total_sum: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Least-significant sum bit matches the full-adder XOR equation.
    check_lsb_sum_bit: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Adding zero with no carry-in passes A through unchanged.
    check_add_zero_to_a: assert property (
        @(posedge clk) ((B == 4'h0) && !Cin) |-> ({Cout, S} == {1'b0, A})
    );

    // Adding zero with no carry-in passes B through unchanged.
    check_add_zero_to_b: assert property (
        @(posedge clk) ((A == 4'h0) && !Cin) |-> ({Cout, S} == {1'b0, B})
    );

    // Zero plus zero with carry-in produces one without carry-out.
    check_zero_plus_zero_with_cin: assert property (
        @(posedge clk) ((A == 4'h0) && (B == 4'h0) && Cin) |-> ({Cout, S} == 5'h01)
    );

    // With B at zero, Cin increments A by one.
    check_increment_a_when_b_zero: assert property (
        @(posedge clk) ((B == 4'h0) && Cin) |-> ({Cout, S} == ({1'b0, A} + 5'd1))
    );

    // Complementary operands with no carry-in sum to all ones with no carry-out.
    check_complementary_operands: assert property (
        @(posedge clk) ((A == ~B) && !Cin) |-> ({Cout, S} == 5'h0F)
    );

    // Adding 1 to 0xF produces zero with carry-out.
    check_f_plus_one: assert property (
        @(posedge clk) ((A == 4'hF) && (B == 4'h1) && !Cin) |-> ({Cout, S} == 5'h10)
    );

    // Maximum inputs produce the maximum 5-bit result.
    check_max_inputs: assert property (
        @(posedge clk) ((A == 4'hF) && (B == 4'hF) && Cin) |-> ({Cout, S} == 5'h1F)
    );

    // Carry-out is high exactly when the 4-bit addition overflows.
    check_carry_out_overflow: assert property (
        @(posedge clk) Cout == ((({1'b0, A} + {1'b0, B} + Cin) >= 5'd16))
    );

endmodule