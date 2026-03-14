module four_to_one_sva (
    input logic CLK,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic X
);
    // No clock/reset in RTL; pure combinational; assertions use external CLK.
    // Functional equation of X.
    check_functional_equation: assert property (
        @(posedge CLK) X == (((A1 ^ A2) & (B1 ^ B2)) ^ A2)
    );
    // When A1 equals A2, X equals A2.
    check_x_eq_a2_when_a1_eq_a2: assert property (
        @(posedge CLK) (A1 == A2) |-> (X == A2)
    );
    // When B1 equals B2, X equals A2.
    check_x_eq_a2_when_b1_eq_b2: assert property (
        @(posedge CLK) (B1 == B2) |-> (X == A2)
    );
    // When both pairs differ, X equals ~A2.
    check_x_eq_not_a2_when_both_xor_ones: assert property (
        @(posedge CLK) ((A1 ^ A2) && (B1 ^ B2)) |-> (X == ~A2)
    );
    // If A2=0 and A1=0 then X=0.
    check_case_a2_0_a1_0_x0: assert property (
        @(posedge CLK) (A2 == 1'b0 && A1 == 1'b0) |-> (X == 1'b0)
    );
    // If A2=0 and A1=1 then X=B1^B2.
    check_case_a2_0_a1_1_x_bxor: assert property (
        @(posedge CLK) (A2 == 1'b0 && A1 == 1'b1) |-> (X == (B1 ^ B2))
    );
    // If A2=1 and A1=1 then X=1.
    check_case_a2_1_a1_1_x1: assert property (
        @(posedge CLK) (A2 == 1'b1 && A1 == 1'b1) |-> (X == 1'b1)
    );
    // If A2=1 and A1=0 then X=~(B1^B2).
    check_case_a2_1_a1_0_x_nbxor: assert property (
        @(posedge CLK) (A2 == 1'b1 && A1 == 1'b0) |-> (X == ~(B1 ^ B2))
    );
    // X==A2 iff at least one input pair is equal.
    check_equivalence_x_eq_a2_iff_either_xor_zero: assert property (
        @(posedge CLK) (X == A2) == ((A1 == A2) || (B1 == B2))
    );
    // Equivalent conditional form based on A2.
    check_conditional_form: assert property (
        @(posedge CLK) X == (A2 ? (A1 | ~(B1 ^ B2)) : (A1 & (B1 ^ B2)))
    );
endmodule