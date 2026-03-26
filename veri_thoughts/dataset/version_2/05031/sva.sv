module adder_4bit_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);

    // The combined outputs must equal A + B + Cin.
    check_total_sum: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // The least-significant sum bit must match the first full-adder XOR.
    check_lsb_sum: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // When A is zero, the result must be B plus Cin.
    check_zero_a_passthrough: assert property (
        @(posedge clk) (A == 4'h0) |-> ({Cout, S} == ({1'b0, B} + Cin))
    );

    // When B is zero, the result must be A plus Cin.
    check_zero_b_passthrough: assert property (
        @(posedge clk) (B == 4'h0) |-> ({Cout, S} == ({1'b0, A} + Cin))
    );

    // Complementary operands with no carry-in must sum to all ones.
    check_complementary_no_carryin: assert property (
        @(posedge clk) ((A == ~B) && !Cin) |-> ((S == 4'hF) && !Cout)
    );

    // Complementary operands with carry-in must wrap to zero with carry-out.
    check_complementary_with_carryin: assert property (
        @(posedge clk) ((A == ~B) && Cin) |-> ((S == 4'h0) && Cout)
    );

    // Maximum inputs with carry-in must produce 5'b1_1111.
    check_maximum_sum: assert property (
        @(posedge clk) ((A == 4'hF) && (B == 4'hF) && Cin) |-> ((S == 4'hF) && Cout)
    );

    // Zero operands must only propagate Cin into bit 0.
    check_all_zero_inputs: assert property (
        @(posedge clk) ((A == 4'h0) && (B == 4'h0)) |-> ((S == {3'b000, Cin}) && !Cout)
    );

    // An extended sum of 16 or more must assert carry-out.
    check_overflow_sets_cout: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B} + Cin) >= 5'd16) |-> Cout
    );

    // An extended sum below 16 must deassert carry-out.
    check_no_overflow_clears_cout: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B} + Cin) <= 5'd15) |-> !Cout
    );

endmodule