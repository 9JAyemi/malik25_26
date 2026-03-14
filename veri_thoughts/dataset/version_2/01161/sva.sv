module FourBitAdder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] Sum,
    input logic Cout
);
    // Sum/Cout equal the 5-bit addition of A, B, and Cin.
    check_add_equivalence: assert property (
        @(posedge CLK) {Cout, Sum} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // LSB sum is XOR of A[0], B[0], Cin.
    check_lsb_sum_xor: assert property (
        @(posedge CLK) Sum[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Carry into bit1 equals A1^B1^Sum1 (i.e., Sum1 = A1^B1^c1).
    check_sum1_matches_c1: assert property (
        @(posedge CLK) (A[1] ^ B[1] ^ Sum[1]) == ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin))
    );

    // Carry into bit2 equals A2^B2^Sum2 using ripple from bit0/bit1.
    check_sum2_matches_c2: assert property (
        @(posedge CLK) (A[2] ^ B[2] ^ Sum[2]) ==
            ((A[1] & B[1]) | ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin))))
    );

    // Carry into bit3 equals A3^B3^Sum3 using ripple from bits0..2.
    check_sum3_matches_c3: assert property (
        @(posedge CLK) (A[3] ^ B[3] ^ Sum[3]) ==
            ((A[2] & B[2]) | ((A[2] ^ B[2]) &
               ((A[1] & B[1]) | ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin))))))
    );

    // Final carry-out equals ripple carry c4 from bits0..3.
    check_cout_matches_c4: assert property (
        @(posedge CLK) Cout ==
            ((A[3] & B[3]) | ((A[3] ^ B[3]) &
               ((A[2] & B[2]) | ((A[2] ^ B[2]) &
                  ((A[1] & B[1]) | ((A[1] ^ B[1]) &
                     ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin))))))))
    );

    // Cout is high iff the 5-bit sum exceeds 15.
    check_cout_overflow_indicator: assert property (
        @(posedge CLK) Cout == (({1'b0, A} + {1'b0, B} + Cin) > 5'd15)
    );

    // Sum equals the low 4 bits of the 5-bit sum.
    check_sum_lower_bits_match: assert property (
        @(posedge CLK) Sum == ({1'b0, A} + {1'b0, B} + Cin)[3:0]
    );

    // When B==0 and Cin==0, pass A through with no carry.
    check_passthrough_A_when_BCin0: assert property (
        @(posedge CLK) (B == 4'b0000 && Cin == 1'b0) |-> (Sum == A && Cout == 1'b0)
    );

    // When A==0 and Cin==0, pass B through with no carry.
    check_passthrough_B_when_ACin0: assert property (
        @(posedge CLK) (A == 4'b0000 && Cin == 1'b0) |-> (Sum == B && Cout == 1'b0)
    );

    // When A==0 and B==0, Sum reflects Cin and no carry out.
    check_zero_plus_zero: assert property (
        @(posedge CLK) (A == 4'b0000 && B == 4'b0000) |-> (Sum == {3'b000, Cin} && Cout == 1'b0)
    );
endmodule