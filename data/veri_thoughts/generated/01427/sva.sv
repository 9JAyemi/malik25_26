module ripple_carry_adder_sva (
    input  logic        CLK,
    input  logic [3:0]  A,
    input  logic [3:0]  B,
    input  logic        CIN,
    input  logic [3:0]  SUM,
    input  logic        COUT
);
    // SUM and COUT equal the 5-bit arithmetic sum of A + B + CIN.
    check_total_sum: assert property (
        @(posedge CLK) {COUT, SUM} == ({1'b0, A} + {1'b0, B} + CIN)
    );

    // LSB: SUM[0] is XOR of A[0], B[0], and CIN.
    check_sum_bit0_xor: assert property (
        @(posedge CLK) SUM[0] == (A[0] ^ B[0] ^ CIN)
    );

    // SUM[1] equals XOR of A[1], B[1], and carry from bit 0.
    check_sum_bit1_ripple: assert property (
        @(posedge CLK)
            SUM[1] == ((A[1] ^ B[1]) ^ ((A[0] & B[0]) | ((A[0] ^ B[0]) & CIN)))
    );

    // SUM[2] equals XOR of A[2], B[2], and carry from bit 1.
    check_sum_bit2_ripple: assert property (
        @(posedge CLK)
            SUM[2] == ((A[2] ^ B[2]) ^
                       ( (A[1] & B[1]) |
                         ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & CIN))) ))
    );

    // SUM[3] equals XOR of A[3], B[3], and carry from bit 2.
    check_sum_bit3_ripple: assert property (
        @(posedge CLK)
            SUM[3] == ((A[3] ^ B[3]) ^
                       ( (A[2] & B[2]) |
                         ((A[2] ^ B[2]) &
                           ( (A[1] & B[1]) |
                             ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & CIN))) ))))
    );

    // COUT equals ripple carry from MSB based on A, B, CIN.
    check_cout_ripple: assert property (
        @(posedge CLK)
            COUT == ( (A[3] & B[3]) |
                      ((A[3] ^ B[3]) &
                        ( (A[2] & B[2]) |
                          ((A[2] ^ B[2]) &
                            ( (A[1] & B[1]) |
                              ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & CIN))) )))))
    );

    // Adding zero (B=0, CIN=0) passes A through with no carry.
    check_zero_identity_B: assert property (
        @(posedge CLK) ((B == 4'b0000) && (CIN == 1'b0)) |-> ((SUM == A) && (COUT == 1'b0))
    );

    // Adding zero (A=0, CIN=0) passes B through with no carry.
    check_zero_identity_A: assert property (
        @(posedge CLK) ((A == 4'b0000) && (CIN == 1'b0)) |-> ((SUM == B) && (COUT == 1'b0))
    );

    // With B=0 and CIN=1, result is A+1 with proper carry-out.
    check_increment_by_cin: assert property (
        @(posedge CLK) ((B == 4'b0000) && (CIN == 1'b1)) |-> ({COUT, SUM} == ({1'b0, A} + 5'd1))
    );

    // Corner case: 15 + 15 + 0 -> SUM=14 and COUT=1.
    check_corner_max_plus_max: assert property (
        @(posedge CLK) ((A == 4'hF) && (B == 4'hF) && (CIN == 1'b0)) |-> ((SUM == 4'hE) && (COUT == 1'b1))
    );

    // Outputs are stable when inputs are stable across cycles.
    check_output_stability: assert property (
        @(posedge CLK) disable iff ($initstate)
            (A == $past(A) && B == $past(B) && CIN == $past(CIN))
            |-> (SUM == $past(SUM) && COUT == $past(COUT))
    );
endmodule