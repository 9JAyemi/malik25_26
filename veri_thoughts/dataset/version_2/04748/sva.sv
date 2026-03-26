module four_bit_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] Sum,
    input logic Cout
);

    // Sum and carry must match 4-bit addition with carry-in.
    check_full_add_result: assert property (
        @(posedge clk) {Cout, Sum} == ({1'b0, A} + {1'b0, B} + {4'b0, Cin})
    );

    // Carry-out must indicate overflow of the 4-bit addition.
    check_cout_matches_overflow: assert property (
        @(posedge clk) Cout == (({1'b0, A} + {1'b0, B} + {4'b0, Cin}) > 5'd15)
    );

    // Bit 0 sum must implement the full-adder XOR equation.
    check_lsb_sum_equation: assert property (
        @(posedge clk) Sum[0] == (A[0] ^ B[0] ^ Cin)
    );

    // With B and carry-in low, the adder must pass A through.
    check_a_passthrough_when_b_zero: assert property (
        @(posedge clk) ((B == 4'h0) && (Cin == 1'b0)) |-> ({Cout, Sum} == {1'b0, A})
    );

    // With A and carry-in low, the adder must pass B through.
    check_b_passthrough_when_a_zero: assert property (
        @(posedge clk) ((A == 4'h0) && (Cin == 1'b0)) |-> ({Cout, Sum} == {1'b0, B})
    );

    // With both operands zero, only the carry-in contributes to the sum.
    check_cin_only_when_inputs_zero: assert property (
        @(posedge clk) ((A == 4'h0) && (B == 4'h0)) |-> ((Sum == {3'b000, Cin}) && (Cout == 1'b0))
    );

    // Complementary operands with no carry-in must sum to all ones.
    check_complementary_inputs_no_carry: assert property (
        @(posedge clk) ((A == ~B) && (Cin == 1'b0)) |-> ({Cout, Sum} == 5'h0F)
    );

    // Complementary operands with carry-in must wrap to zero and assert carry-out.
    check_complementary_inputs_with_carry: assert property (
        @(posedge clk) ((A == ~B) && (Cin == 1'b1)) |-> ({Cout, Sum} == 5'h10)
    );

    // Maximum inputs with carry-in must produce the saturated 5-bit result.
    check_all_ones_plus_cin: assert property (
        @(posedge clk) ((A == 4'hF) && (B == 4'hF) && (Cin == 1'b1)) |-> ({Cout, Sum} == 5'h1F)
    );

endmodule