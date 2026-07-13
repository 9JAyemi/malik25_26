module adder_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CIN,
    input logic [3:0] SUM,
    input logic COUT
);
    // No clock/reset in DUT; purely combinational. Sample on posedges of any input.

    // Helper carry chain expressions (combinational).
    let c1 = (A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN);
    let c2 = (A[1] & B[1]) | (A[1] & c1) | (B[1] & c1);
    let c3 = (A[2] & B[2]) | (A[2] & c2) | (B[2] & c2);
    let c4 = (A[3] & B[3]) | (A[3] & c3) | (B[3] & c3);

    ///// Functional correctness /////
    // Full 5-bit sum equals A + B + CIN.
    check_fullsum_vector: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or
          posedge B[0] or posedge B[1] or posedge B[2] or posedge B[3] or
          posedge CIN)
        {COUT, SUM} == ({1'b0, A} + {1'b0, B} + CIN)
    );

    // LSB SUM bit is XOR of A[0], B[0], and CIN.
    check_sum0_xor: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or
          posedge B[0] or posedge B[1] or posedge B[2] or posedge B[3] or
          posedge CIN)
        SUM[0] == (A[0] ^ B[0] ^ CIN)
    );

    // SUM[1] uses ripple carry c1.
    check_sum1_ripple: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or
          posedge B[0] or posedge B[1] or posedge B[2] or posedge B[3] or
          posedge CIN)
        SUM[1] == (A[1] ^ B[1] ^ c1)
    );

    // SUM[2] uses ripple carry c2.
    check_sum2_ripple: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or
          posedge B[0] or posedge B[1] or posedge B[2] or posedge B[3] or
          posedge CIN)
        SUM[2] == (A[2] ^ B[2] ^ c2)
    );

    // SUM[3] uses ripple carry c3.
    check_sum3_ripple: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or
          posedge B[0] or posedge B[1] or posedge B[2] or posedge B[3] or
          posedge CIN)
        SUM[3] == (A[3] ^ B[3] ^ c3)
    );

    // Final carry-out equals ripple carry c4.
    check_cout_ripple: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or
          posedge B[0] or posedge B[1] or posedge B[2] or posedge B[3] or
          posedge CIN)
        COUT == c4
    );

    ///// Useful corner cases /////
    // With CIN == 0, sum equals A + B.
    check_no_cin_sum: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or
          posedge B[0] or posedge B[1] or posedge B[2] or posedge B[3] or
          posedge CIN)
        (CIN == 1'b0) |-> ({COUT, SUM} == ({1'b0, A} + {1'b0, B}))
    );

    // When B == 0 and CIN == 0, SUM passes A and COUT is 0.
    check_pass_A_when_B0_CIN0: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or
          posedge B[0] or posedge B[1] or posedge B[2] or posedge B[3] or
          posedge CIN)
        ((B == 4'b0000) && (CIN == 1'b0)) |-> ((SUM == A) && (COUT == 1'b0))
    );

    // When A == 0 and CIN == 0, SUM passes B and COUT is 0.
    check_pass_B_when_A0_CIN0: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or
          posedge B[0] or posedge B[1] or posedge B[2] or posedge B[3] or
          posedge CIN)
        ((A == 4'b0000) && (CIN == 1'b0)) |-> ((SUM == B) && (COUT == 1'b0))
    );

    // When A == 0 and B == 0, SUM equals CIN in bit0 and COUT is 0.
    check_zero_plus_zero: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or
          posedge B[0] or posedge B[1] or posedge B[2] or posedge B[3] or
          posedge CIN)
        ((A == 4'b0000) && (B == 4'b0000)) |-> ((SUM == {3'b000, CIN}) && (COUT == 1'b0))
    );

    // COUT is 1 iff the 5-bit sum overflows 4 bits (>= 16).
    check_cout_on_overflow: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or
          posedge B[0] or posedge B[1] or posedge B[2] or posedge B[3] or
          posedge CIN)
        (({1'b0, A} + {1'b0, B} + CIN) >= 5'd16) |-> (COUT == 1'b1)
    );

    // No overflow implies COUT is 0.
    check_cout_no_overflow: assert property (
        @(posedge A[0] or posedge A[1] or posedge A[2] or posedge A[3] or
          posedge B[0] or posedge B[1] or posedge B[2] or posedge B[3] or
          posedge CIN)
        (({1'b0, A} + {1'b0, B} + CIN) <= 5'd15) |-> (COUT == 1'b0)
    );
endmodule