module sky130_fd_sc_hdll__and3_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C
);
    // No clock/reset in RTL; pure combinational AND3 with buffer to X.
    // Assertions are sampled on any edge of A, B, C, or X.

    // X must equal A & B & C at all times.
    check_functional_equivalence: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge X or negedge X)
            X == (A & B & C)
    );

    // If any input is 0, X must be 0.
    check_zero_dominance: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge X or negedge X)
            ((!A) || (!B) || (!C)) |-> (X == 1'b0)
    );

    // If all inputs are 1, X must be 1.
    check_all_high_implies_one: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge X or negedge X)
            (A && B && C) |-> (X == 1'b1)
    );

    // A&B high makes X follow C.
    check_ab_high_passthru_c: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge X or negedge X)
            (A && B) |-> (X == C)
    );

    // A&C high makes X follow B.
    check_ac_high_passthru_b: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge X or negedge X)
            (A && C) |-> (X == B)
    );

    // B&C high makes X follow A.
    check_bc_high_passthru_a: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge X or negedge X)
            (B && C) |-> (X == A)
    );

    // A rising transition of the 3-input AND forces X to rise.
    check_and_rise_causes_x_rise: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge X or negedge X)
            $rose(A && B && C) |-> $rose(X)
    );

    // A falling transition of the 3-input AND forces X to fall.
    check_and_fall_causes_x_fall: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge X or negedge X)
            $fell(A && B && C) |-> $fell(X)
    );

    // X can only rise when all inputs are 1.
    check_x_rise_requires_all_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge X or negedge X)
            $rose(X) |-> (A && B && C)
    );

    // X can only fall when not all inputs are 1.
    check_x_fall_requires_not_all_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge X or negedge X)
            $fell(X) |-> !(A && B && C)
    );

    // Any change on X must be due to a change on at least one input.
    check_x_change_requires_input_change: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge X or negedge X)
            $changed(X) |-> ($changed(A) || $changed(B) || $changed(C))
    );

endmodule