module adder_4bit_assertions (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic Cout
);

    // LSB sum is the XOR of A[0] and B[0].
    check_sum_bit0_xor: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0])
    );

    // Sum bit 1 matches the 2-bit addition of the lower slices.
    check_sum_bit1_lower_add: assert property (
        @(posedge clk) S[1] == (({1'b0, A[1:0]} + {1'b0, B[1:0]})[1])
    );

    // Sum bit 2 matches the 3-bit addition of the lower slices.
    check_sum_bit2_lower_add: assert property (
        @(posedge clk) S[2] == (({1'b0, A[2:0]} + {1'b0, B[2:0]})[2])
    );

    // Sum bit 3 matches the 4-bit addition result.
    check_sum_bit3_full_add: assert property (
        @(posedge clk) S[3] == (({1'b0, A} + {1'b0, B})[3])
    );

    // Cout matches the carry-out of the 4-bit addition.
    check_cout_full_add: assert property (
        @(posedge clk) Cout == (({1'b0, A} + {1'b0, B})[4])
    );

    // The full 5-bit output matches A plus B.
    check_full_result_addition: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B})
    );

    // Adding zero on B leaves A unchanged.
    check_zero_identity_on_b: assert property (
        @(posedge clk) (B == 4'b0000) |-> ({Cout, S} == {1'b0, A})
    );

    // Adding zero on A leaves B unchanged.
    check_zero_identity_on_a: assert property (
        @(posedge clk) (A == 4'b0000) |-> ({Cout, S} == {1'b0, B})
    );

endmodule