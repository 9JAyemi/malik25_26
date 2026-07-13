module fourBitAdder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] Sum,
    input logic Cout
);

    // Combined output must equal the 5-bit sum of A, B, and Cin.
    check_combined_result: assert property (
        @(posedge clk) {Cout, Sum} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // The least-significant sum bit must match A[0] xor B[0] xor Cin.
    check_lsb_xor_behavior: assert property (
        @(posedge clk) Sum[0] == (A[0] ^ B[0] ^ Cin)
    );

    // With both operands zero, the output must only reflect Cin.
    check_zero_operands_cin_only: assert property (
        @(posedge clk) (A == 4'h0 && B == 4'h0) |-> ({Cout, Sum} == {4'b0000, Cin})
    );

    // With A zero and Cin low, the output must pass B through with no carry.
    check_a_zero_b_passthrough: assert property (
        @(posedge clk) (A == 4'h0 && Cin == 1'b0) |-> ({Cout, Sum} == {1'b0, B})
    );

    // With B zero and Cin low, the output must pass A through with no carry.
    check_b_zero_a_passthrough: assert property (
        @(posedge clk) (B == 4'h0 && Cin == 1'b0) |-> ({Cout, Sum} == {1'b0, A})
    );

    // Carry-out must be low when the computed sum fits in 4 bits.
    check_no_overflow_no_carry: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B} + Cin) <= 5'd15) |-> (Cout == 1'b0)
    );

    // Carry-out must be high when the computed sum exceeds 4 bits.
    check_overflow_sets_carry: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B} + Cin) >= 5'd16) |-> (Cout == 1'b1)
    );

    // The maximum input combination must produce the maximum 5-bit result.
    check_maximum_input_sum: assert property (
        @(posedge clk) (A == 4'hF && B == 4'hF && Cin == 1'b1) |-> ({Cout, Sum} == 5'h1F)
    );

endmodule