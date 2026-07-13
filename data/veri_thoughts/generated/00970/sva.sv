module mux_2to1_sva (
    input logic clk,
    input logic A0,
    input logic A1,
    input logic S,
    input logic X
);
    // X equals A0 when S=0, else A1 (functional equivalence).
    check_mux_truth_table: assert property (
        @(posedge clk) X == ((S == 1'b0) ? A0 : A1)
    );

    // When S=0 and only A1 changes, X must remain unchanged.
    check_unselected_change_no_effect_S0: assert property (
        @(posedge clk) (S == 1'b0) && $changed(A1) && $stable(A0) && $stable(S) |-> $stable(X)
    );

    // When S=1 and only A0 changes, X must remain unchanged.
    check_unselected_change_no_effect_S1: assert property (
        @(posedge clk) (S == 1'b1) && $changed(A0) && $stable(A1) && $stable(S) |-> $stable(X)
    );

    // When S=0 and A0 changes (others stable), X must equal A0.
    check_selected_change_reflected_S0: assert property (
        @(posedge clk) (S == 1'b0) && $changed(A0) && $stable(A1) && $stable(S) |-> (X == A0)
    );

    // When S=1 and A1 changes (others stable), X must equal A1.
    check_selected_change_reflected_S1: assert property (
        @(posedge clk) (S == 1'b1) && $changed(A1) && $stable(A0) && $stable(S) |-> (X == A1)
    );

    // On S rising edge, X must equal A1.
    check_select_rise_routes_A1: assert property (
        @(posedge clk) $rose(S) |-> (X == A1)
    );

    // On S falling edge, X must equal A0.
    check_select_fall_routes_A0: assert property (
        @(posedge clk) $fell(S) |-> (X == A0)
    );

    // If A0 equals A1, X must equal that value regardless of S.
    check_equal_inputs_drive_x: assert property (
        @(posedge clk) (A0 == A1) |-> (X == A0)
    );

    // If S, A0, and A1 are stable, X must be stable.
    check_stable_inputs_hold_output: assert property (
        @(posedge clk) $stable({S, A0, A1}) |-> $stable(X)
    );

    // If X changes, at least one of S, A0, or A1 must have changed.
    check_output_change_requires_input_change: assert property (
        @(posedge clk) $changed(X) |-> ($changed(S) || $changed(A0) || $changed(A1))
    );
endmodule