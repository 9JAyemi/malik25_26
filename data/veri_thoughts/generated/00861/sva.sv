module adder32_sva (
    input logic CLK,
    input logic a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
    input logic b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
    input logic s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15,
    input logic cout
);
    // DUT is purely combinational; no clock/reset in RTL. Assertions sample on CLK; no reset disable.

    // Assemble vectors for convenience
    logic [15:0] A, B, Sbits;
    logic [16:0] expected_sum;
    assign A = {a15,a14,a13,a12,a11,a10,a9,a8,a7,a6,a5,a4,a3,a2,a1,a0};
    assign B = {b15,b14,b13,b12,b11,b10,b9,b8,b7,b6,b5,b4,b3,b2,b1,b0};
    assign Sbits = {s15,s14,s13,s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,s0};
    assign expected_sum = {1'b0, A} + {1'b0, B};

    ///// Functional correctness /////
    // Full 17-bit result must equal unsigned A+B.
    check_fullsum_matches_addition: assert property (
        @(posedge CLK) disable iff (1'b0) {cout, Sbits} == expected_sum
    );

    // LSB sum is XOR of LSB inputs (no carry-in).
    check_s0_is_xor: assert property (
        @(posedge CLK) disable iff (1'b0) s0 == (a0 ^ b0)
    );

    // MSB of sum must match expected_sum[15].
    check_s15_matches_expected: assert property (
        @(posedge CLK) disable iff (1'b0) s15 == expected_sum[15]
    );

    ///// Corner cases /////
    // Adding zero on B side passes A through with no carry.
    check_add_zero_B: assert property (
        @(posedge CLK) disable iff (1'b0) (B == 16'h0000) |-> ({cout, Sbits} == {1'b0, A})
    );

    // Adding zero on A side passes B through with no carry.
    check_add_zero_A: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 16'h0000) |-> ({cout, Sbits} == {1'b0, B})
    );

    // Adding bitwise complement yields all 1s with no carry.
    check_add_complement: assert property (
        @(posedge CLK) disable iff (1'b0) (B == ~A) |-> ({cout, Sbits} == {1'b0, 16'hFFFF})
    );

    // Adding 1 on B increments A by 1.
    check_add_one_B: assert property (
        @(posedge CLK) disable iff (1'b0) (B == 16'h0001) |-> ({cout, Sbits} == ({1'b0, A} + 17'd1))
    );

    // Adding 1 on A increments B by 1.
    check_add_one_A: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 16'h0001) |-> ({cout, Sbits} == ({1'b0, B} + 17'd1))
    );

    ///// Carry behavior (unsigned) /////
    // If carry-out is 1, the truncated sum is less than at least one operand.
    check_cout_implies_sum_less_operand: assert property (
        @(posedge CLK) disable iff (1'b0) cout |-> ((Sbits < A) || (Sbits < B))
    );

    // If carry-out is 0, the truncated sum is >= both operands.
    check_no_cout_implies_sum_ge_operands: assert property (
        @(posedge CLK) disable iff (1'b0) !cout |-> ((Sbits >= A) && (Sbits >= B))
    );

endmodule