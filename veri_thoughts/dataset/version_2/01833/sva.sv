module adder4_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic Cout
);
    // Outputs represent the 5-bit sum of A and B (no carry-in).
    check_sum_matches_add: assert property (
        @(posedge clk) {Cout, S} == (A + B)
    );

    // LSB sum is XOR of inputs (Cin=0).
    check_s0_is_xor: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0])
    );

    // Bit1 sum equals XOR with carry from bit0 (A0&B0).
    check_s1_is_xor_with_carry: assert property (
        @(posedge clk) S[1] == ((A[1] ^ B[1]) ^ (A[0] & B[0]))
    );

    // Bit2 sum equals XOR with propagated carry C2.
    check_s2_is_xor_with_carry: assert property (
        @(posedge clk) S[2] == ((A[2] ^ B[2]) ^ ( (A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0])) ))
    );

    // Bit3 sum equals XOR with propagated carry C3.
    check_s3_is_xor_with_carry: assert property (
        @(posedge clk) S[3] == ((A[3] ^ B[3]) ^ ( (A[2] & B[2]) | ((A[2] ^ B[2]) & ( (A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0])) )) ))
    );

    // Cout equals the final carry-out from bit3.
    check_cout_is_final_carry: assert property (
        @(posedge clk) Cout == ( (A[3] & B[3]) | ((A[3] ^ B[3]) & ( (A[2] & B[2]) | ((A[2] ^ B[2]) & ( (A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0])) )) )) )
    );

    // Adding zero to zero yields zero sum and no carry.
    check_zero_plus_zero: assert property (
        @(posedge clk) ((A == 4'd0) && (B == 4'd0)) |-> ((S == 4'd0) && (Cout == 1'b0))
    );

    // Adding zero (B) passes A to S with no carry.
    check_add_zero_b: assert property (
        @(posedge clk) (B == 4'd0) |-> ((S == A) && (Cout == 1'b0))
    );

    // Adding zero (A) passes B to S with no carry.
    check_add_zero_a: assert property (
        @(posedge clk) (A == 4'd0) |-> ((S == B) && (Cout == 1'b0))
    );

    // A plus bitwise-not A yields 0xF with no carry.
    check_a_plus_not_a: assert property (
        @(posedge clk) (B == ~A) |-> ((S == 4'hF) && (Cout == 1'b0))
    );
endmodule