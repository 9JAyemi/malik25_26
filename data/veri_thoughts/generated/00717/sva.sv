module sky130_fd_sc_hdll__a31o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);
    // X equals (A1&A2&A3) OR B1.
    check_function_equivalence: assert property (
        @(posedge $global_clock) X == ((A1 & A2 & A3) | B1)
    );

    // B1 high forces X high.
    check_B1_dominates: assert property (
        @(posedge $global_clock) B1 |-> X
    );

    // When B1 is low, X equals A1&A2&A3.
    check_B1_low_defines_and_path: assert property (
        @(posedge $global_clock) !B1 |-> (X == (A1 & A2 & A3))
    );

    // All A inputs high forces X high.
    check_all_A_high_sets_X: assert property (
        @(posedge $global_clock) (A1 & A2 & A3) |-> X
    );

    // X high implies B1 is high or all A are high.
    check_X_high_causality: assert property (
        @(posedge $global_clock) X |-> (B1 | (A1 & A2 & A3))
    );

    // X low implies B1 is low and not all A are high.
    check_X_low_causality: assert property (
        @(posedge $global_clock) !X |-> (!B1 && !(A1 & A2 & A3))
    );

    // If B1 is low and A1 is low, X must be low.
    check_A1_zero_forces_X0_when_B1_zero: assert property (
        @(posedge $global_clock) (!B1 && !A1) |-> !X
    );

    // If B1 is low and A2 is low, X must be low.
    check_A2_zero_forces_X0_when_B1_zero: assert property (
        @(posedge $global_clock) (!B1 && !A2) |-> !X
    );

    // If B1 is low and A3 is low, X must be low.
    check_A3_zero_forces_X0_when_B1_zero: assert property (
        @(posedge $global_clock) (!B1 && !A3) |-> !X
    );

    // With inputs stable across a cycle, X remains stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge $global_clock) ($stable(A1) && $stable(A2) && $stable(A3) && $stable(B1)) |-> $stable(X)
    );
endmodule