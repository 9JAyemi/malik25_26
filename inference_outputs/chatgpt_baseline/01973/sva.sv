module sky130_fd_sc_lp__o31a_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);
    // X implements ((A1|A2|A3) & B1) on any input/output transition.
    check_function_equivalence: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge X or negedge X)
            X == ((A1 || A2 || A3) && B1)
    );

    // X high implies B1 high.
    check_x_implies_b1: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge X or negedge X)
            X |-> B1
    );

    // X high implies at least one of A1/A2/A3 high.
    check_x_implies_any_ai: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge X or negedge X)
            X |-> (A1 || A2 || A3)
    );

    // B1 low forces X low.
    check_b1_low_forces_x0: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge X or negedge X)
            !B1 |-> (X == 1'b0)
    );

    // B1 high makes X equal to A1|A2|A3.
    check_b1_high_matches_or: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge X or negedge X)
            B1 |-> (X == (A1 || A2 || A3))
    );

    // If B1 and A1 are high, X must be high.
    check_b1_and_a1_implies_x1: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge X or negedge X)
            (B1 && A1) |-> X
    );

    // If B1 and A2 are high, X must be high.
    check_b1_and_a2_implies_x1: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge X or negedge X)
            (B1 && A2) |-> X
    );

    // If B1 and A3 are high, X must be high.
    check_b1_and_a3_implies_x1: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge X or negedge X)
            (B1 && A3) |-> X
    );

    // If B1 is high and X is low, then all A1/A2/A3 must be low.
    check_b1_high_x0_implies_all_ai0: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge X or negedge X)
            (B1 && (X == 1'b0)) |-> (!A1 && !A2 && !A3)
    );

    // If all A1/A2/A3 are low, X must be low regardless of B1.
    check_all_ai0_forces_x0: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge X or negedge X)
            (!A1 && !A2 && !A3) |-> (X == 1'b0)
    );
endmodule