module sky130_fd_sc_lp__o221a_sva (
    input logic CLK,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);
    // X equals (A1|A2) & (B1|B2) & C1.
    check_function_equivalence: assert property (
        @(posedge CLK) X == ((A1 | A2) & (B1 | B2) & C1)
    );

    // X high requires C1 high.
    check_x_implies_c1: assert property (
        @(posedge CLK) X |-> (C1 == 1'b1)
    );

    // X high requires at least one of A1/A2 high.
    check_x_implies_a_group: assert property (
        @(posedge CLK) X |-> ((A1 | A2) == 1'b1)
    );

    // X high requires at least one of B1/B2 high.
    check_x_implies_b_group: assert property (
        @(posedge CLK) X |-> ((B1 | B2) == 1'b1)
    );

    // C1 low forces X low.
    check_c1_low_forces_x0: assert property (
        @(posedge CLK) (C1 == 1'b0) |-> (X == 1'b0)
    );

    // Both A1 and A2 low force X low.
    check_a_group_zero_forces_x0: assert property (
        @(posedge CLK) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (X == 1'b0)
    );

    // Both B1 and B2 low force X low.
    check_b_group_zero_forces_x0: assert property (
        @(posedge CLK) ((B1 == 1'b0) && (B2 == 1'b0)) |-> (X == 1'b0)
    );

    // When C1 rises and both groups are high, X must rise.
    check_x_rise_on_c1_rise_with_groups_high: assert property (
        @(posedge CLK) ($rose(C1) && (A1 | A2) && (B1 | B2)) |-> $rose(X)
    );

    // When C1 falls from 1 and both groups were 1, X must fall.
    check_x_fall_on_c1_fall_with_groups_prev_high: assert property (
        @(posedge CLK) ($fell(C1) && $past(A1 | A2) && $past(B1 | B2)) |-> $fell(X)
    );

    // If all inputs are stable, X must be stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable({A1,A2,B1,B2,C1}) |-> $stable(X)
    );
endmodule