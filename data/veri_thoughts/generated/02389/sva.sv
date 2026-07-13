module sky130_fd_sc_hd__o2bb2a_sva (
    input  logic CLK,   // external sample clock for assertions
    input  logic A1_N,
    input  logic A2_N,
    input  logic B1,
    input  logic B2,
    input  logic X
);
    // X implements A1_N & ~A2_N & B1 & ~B2.
    check_functional_equivalence: assert property (
        @(posedge CLK) X == (A1_N && !A2_N && B1 && !B2)
    );

    // X can be 1 only when the input pattern holds.
    check_x_high_requires_pattern: assert property (
        @(posedge CLK) X |-> (A1_N && !A2_N && B1 && !B2)
    );

    // When the input pattern holds, X must be 1.
    check_pattern_implies_x_high: assert property (
        @(posedge CLK) (A1_N && !A2_N && B1 && !B2) |-> X
    );

    // A1_N low forces X low.
    check_a1n_zero_forces_x_zero: assert property (
        @(posedge CLK) !A1_N |-> !X
    );

    // A2_N high forces X low.
    check_a2n_one_forces_x_zero: assert property (
        @(posedge CLK) A2_N |-> !X
    );

    // B1 low forces X low.
    check_b1_zero_forces_x_zero: assert property (
        @(posedge CLK) !B1 |-> !X
    );

    // B2 high forces X low.
    check_b2_one_forces_x_zero: assert property (
        @(posedge CLK) B2 |-> !X
    );

    // If inputs are stable, X is stable.
    check_x_stable_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(A1_N) && $stable(A2_N) && $stable(B1) && $stable(B2)) |-> $stable(X)
    );

    // Leaving the pattern via A1_N going low makes X low next cycle.
    check_leave_pattern_via_a1n_drop: assert property (
        @(posedge CLK) (A1_N && !A2_N && B1 && !B2) ##1 (!A1_N) |-> !X
    );

    // Leaving the pattern via A2_N going high makes X low next cycle.
    check_leave_pattern_via_a2n_rise: assert property (
        @(posedge CLK) (A1_N && !A2_N && B1 && !B2) ##1 (A2_N) |-> !X
    );

    // Leaving the pattern via B1 going low makes X low next cycle.
    check_leave_pattern_via_b1_drop: assert property (
        @(posedge CLK) (A1_N && !A2_N && B1 && !B2) ##1 (!B1) |-> !X
    );

    // Leaving the pattern via B2 going high makes X low next cycle.
    check_leave_pattern_via_b2_rise: assert property (
        @(posedge CLK) (A1_N && !A2_N && B1 && !B2) ##1 (B2) |-> !X
    );
endmodule