module addsub_sva (
    input logic [15:0] A,
    input logic [15:0] B,
    input logic       C,
    input logic [15:0] Q
);

    // When C rises (C==1), Q equals A - B (16-bit wrap-around).
    check_sub_on_posedge_c: assert property (
        @(posedge C) Q == (A - B)
    );

    // When C falls (C==0), Q equals A + B (16-bit wrap-around).
    check_add_on_negedge_c: assert property (
        @(negedge C) Q == (A + B)
    );

    // On subtraction selection, adding B back must recover A.
    check_sub_reversibility: assert property (
        @(posedge C) (Q + B) == A
    );

    // On addition selection, subtracting B must recover A.
    check_add_inverse_wrt_B: assert property (
        @(negedge C) (Q - B) == A
    );

    // On addition selection, subtracting A must recover B.
    check_add_inverse_wrt_A: assert property (
        @(negedge C) (Q - A) == B
    );

    // On subtraction selection and A==B, Q must be zero.
    check_sub_zero_when_equal: assert property (
        @(posedge C) (A == B) |-> (Q == 16'd0)
    );

    // On subtraction selection and B==0, Q must equal A.
    check_sub_identity_B_zero: assert property (
        @(posedge C) (B == 16'd0) |-> (Q == A)
    );

    // On addition selection and B==0, Q must equal A.
    check_add_identity_B_zero: assert property (
        @(negedge C) (B == 16'd0) |-> (Q == A)
    );

    // On addition selection and A==0, Q must equal B.
    check_add_identity_A_zero: assert property (
        @(negedge C) (A == 16'd0) |-> (Q == B)
    );

    // On subtraction selection and A==0, Q is two's-negation of B (Q + B == 0).
    check_sub_negation_A_zero: assert property (
        @(posedge C) (A == 16'd0) |-> ((Q + B) == 16'd0)
    );

endmodule