module four_bit_adder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);
    // Helper carry chain computed from inputs
    logic c0, c1, c2;
    assign c0 = (A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin);
    assign c1 = (A[1] & B[1]) | (A[1] & c0)  | (B[1] & c0);
    assign c2 = (A[2] & B[2]) | (A[2] & c1)  | (B[2] & c1);

    // 5-bit full sum for equivalence checking
    logic [4:0] fullsum;
    assign fullsum = {1'b0, A} + {1'b0, B} + Cin;

    ///// Bit-level full-adder relationships /////
    // LSB sum equals XOR of inputs A[0], B[0], Cin.
    check_sum0_xor: assert property (
        @(posedge CLK) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Bit1 sum equals XOR of A[1], B[1], and carry from bit0.
    check_sum1_xor: assert property (
        @(posedge CLK) S[1] == (A[1] ^ B[1] ^ c0)
    );

    // Bit2 sum equals XOR of A[2], B[2], and carry from bit1.
    check_sum2_xor: assert property (
        @(posedge CLK) S[2] == (A[2] ^ B[2] ^ c1)
    );

    // Bit3 sum equals XOR of A[3], B[3], and carry from bit2.
    check_sum3_xor: assert property (
        @(posedge CLK) S[3] == (A[3] ^ B[3] ^ c2)
    );

    // Carry-out equals majority of A[3], B[3], and carry from bit2.
    check_cout_majority: assert property (
        @(posedge CLK) Cout == ((A[3] & B[3]) | (A[3] & c2) | (B[3] & c2))
    );

    ///// Whole-adder equivalence /////
    // {Cout,S} equals 5-bit sum of A, B, and Cin.
    check_fullsum_concat: assert property (
        @(posedge CLK) {Cout, S} == fullsum
    );

    // S equals lower 4 bits of the 5-bit sum.
    check_s_matches_fullsum_lower: assert property (
        @(posedge CLK) S == fullsum[3:0]
    );

    // Cout equals MSB of the 5-bit sum.
    check_cout_matches_fullsum_msb: assert property (
        @(posedge CLK) Cout == fullsum[4]
    );

    ///// Sanity corner cases /////
    // When A and B are zero, S mirrors Cin on bit0 and Cout is zero.
    check_zero_inputs_behavior: assert property (
        @(posedge CLK) (A == 4'b0000 && B == 4'b0000) |=> (S == {3'b000, Cin}) && (Cout == 1'b0)
    );

    // When A and B are all ones, Cout is one and S depends on Cin.
    check_all_ones_behavior: assert property (
        @(posedge CLK) (A == 4'hF && B == 4'hF) |=> (Cout == 1'b1) && (S == (Cin ? 4'hF : 4'hE))
    );
endmodule