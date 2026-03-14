module or4_top_module_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    ///// Functional correctness of OR /////
    // X equals the OR of all four inputs.
    check_x_is_or_all: assert property (
        @($global_clock) X == (A | B | C | D_N)
    );
    // X equals the OR of grouped inputs per structure.
    check_x_is_grouped_or: assert property (
        @($global_clock) X == ((A | B) | (C | D_N))
    );

    ///// Input-to-output implications /////
    // If A is HIGH, X must be HIGH.
    check_a_implies_x_high: assert property (
        @($global_clock) A |-> X
    );
    // If B is HIGH, X must be HIGH.
    check_b_implies_x_high: assert property (
        @($global_clock) B |-> X
    );
    // If C is HIGH, X must be HIGH.
    check_c_implies_x_high: assert property (
        @($global_clock) C |-> X
    );
    // If D_N is HIGH, X must be HIGH.
    check_d_implies_x_high: assert property (
        @($global_clock) D_N |-> X
    );

    ///// Necessary conditions /////
    // If all inputs are LOW, X must be LOW.
    check_all_zero_implies_x_low: assert property (
        @($global_clock) (!A && !B && !C && !D_N) |-> !X
    );
    // If X is HIGH, at least one input must be HIGH.
    check_x_high_has_cause: assert property (
        @($global_clock) X |-> (A || B || C || D_N)
    );

    ///// Stability and sensitivity /////
    // If all inputs are stable, X must be stable.
    check_input_stability_implies_x_stable: assert property (
        @($global_clock) ($stable(A) && $stable(B) && $stable(C) && $stable(D_N)) |-> $stable(X)
    );
    // X can only change if at least one input changes.
    check_x_change_requires_input_change: assert property (
        @($global_clock) $changed(X) |-> ($changed(A) || $changed(B) || $changed(C) || $changed(D_N))
    );
endmodule