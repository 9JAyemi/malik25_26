module binary_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic Cout
);

    ///// Functional correctness /////
    // {Cout,S} equals the 5-bit sum of A and B.
    check_result_matches_addition: assert property (
        @(posedge clk) {Cout, S} == (A + B)
    );

    // S is the low 4 bits of A+B.
    check_S_is_low4_of_sum: assert property (
        @(posedge clk) S == (A + B)[3:0]
    );

    // Cout is the MSB (carry-out) of A+B.
    check_Cout_is_carry_of_sum: assert property (
        @(posedge clk) Cout == (A + B)[4]
    );

    ///// Ripple-carry structure equivalence /////
    // Bit 0 sum: no carry-in.
    check_s0_xor: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0])
    );

    // Bit 1 sum uses carry from bit 0.
    check_s1_rca: assert property (
        @(posedge clk) S[1] == ((A[1] ^ B[1]) ^ (A[0] & B[0]))
    );

    // Bit 2 sum uses carry from bit 1.
    check_s2_rca: assert property (
        @(posedge clk) S[2] == ((A[2] ^ B[2]) ^ (((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0])))))
    );

    // Bit 3 sum uses carry from bit 2.
    check_s3_rca: assert property (
        @(posedge clk) S[3] == ((A[3] ^ B[3]) ^ (((A[2] & B[2]) | ((A[2] ^ B[2]) & ((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0])))))))
    );

    // Final carry-out from bit 3.
    check_cout_rca: assert property (
        @(posedge clk) Cout == ((A[3] & B[3]) | ((A[3] ^ B[3]) & ((A[2] & B[2]) | ((A[2] ^ B[2]) & ((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0])))))))
    );

    ///// Overflow/carry equivalence /////
    // If sum exceeds 4 bits, Cout must be 1.
    check_overflow_sets_cout: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B}) > 5'd15) |-> (Cout == 1'b1)
    );

    // Cout high implies sum exceeds 4 bits.
    check_cout_implies_overflow: assert property (
        @(posedge clk) Cout |-> (({1'b0, A} + {1'b0, B}) > 5'd15)
    );

    ///// Determinism /////
    // If inputs are stable cycle-to-cycle, outputs remain stable.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({A, B}) |-> $stable({S, Cout})
    );

endmodule