module FA_17_sva (
    input logic CLK,
    input logic RESETn,
    input logic A,
    input logic B,
    input logic Ci,
    input logic S,
    input logic Co
);
    // Analysis: No clock/reset in RTL; purely combinational full adder: S=A^B^Ci, Co=(A&B)|((A^B)&Ci). Assertions sampled on CLK, gated by RESETn.

    // Sum equals three-input XOR of A, B, Ci.
    check_sum_is_xor3: assert property (
        @(posedge CLK) disable iff (!RESETn) S == (A ^ B ^ Ci)
    );

    // Carry equals (A&B) | ((A^B)&Ci) as implemented.
    check_carry_definition: assert property (
        @(posedge CLK) disable iff (!RESETn) Co == ((A & B) | ((A ^ B) & Ci))
    );

    // Carry equals majority-of-three equivalent form.
    check_carry_majority_equiv: assert property (
        @(posedge CLK) disable iff (!RESETn) Co == ((A & B) | (A & Ci) | (B & Ci))
    );

    // With Ci=0, sum reduces to A^B and carry to A&B.
    check_ci0_case: assert property (
        @(posedge CLK) disable iff (!RESETn) (Ci == 1'b0) |-> ((S == (A ^ B)) && (Co == (A & B)))
    );

    // With Ci=1, sum is XNOR of A and B; carry is A|B.
    check_ci1_case: assert property (
        @(posedge CLK) disable iff (!RESETn) (Ci == 1'b1) |-> ((S == !(A ^ B)) && (Co == (A | B)))
    );

    // When A equals B, sum equals Ci; carry equals A&B.
    check_a_eq_b_case: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == B) |-> ((S == Ci) && (Co == (A & B)))
    );

    // When A differs from B, sum is ~Ci and carry equals Ci.
    check_a_xor_b_case: assert property (
        @(posedge CLK) disable iff (!RESETn) (A ^ B) |-> ((S == !Ci) && (Co == Ci))
    );

    // If both A and B are 1, carry must be 1 and sum equals Ci.
    check_ab_both1_implies_carry: assert property (
        @(posedge CLK) disable iff (!RESETn) (A & B) |-> ((Co == 1'b1) && (S == Ci))
    );

    // If Ci=1 and exactly one of A,B is 1, carry must be 1.
    check_ci_and_axorb_implies_carry: assert property (
        @(posedge CLK) disable iff (!RESETn) (Ci & (A ^ B)) |-> (Co == 1'b1)
    );

    // All inputs zero produce S=0 and Co=0.
    check_all_zero_case: assert property (
        @(posedge CLK) disable iff (!RESETn) (!(A | B | Ci)) |-> ((S == 1'b0) && (Co == 1'b0))
    );

    // All inputs one produce S=1 and Co=1.
    check_all_one_case: assert property (
        @(posedge CLK) disable iff (!RESETn) (A & B & Ci) |-> ((S == 1'b1) && (Co == 1'b1))
    );
endmodule