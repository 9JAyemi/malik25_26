module mux2_sva (
    input logic clk,
    input logic A0,
    input logic A1,
    input logic S,
    input logic X,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    // X must always match the mux select expression.
    check_mux_function: assert property (
        @(posedge clk) X == (S ? A1 : A0)
    );

    // When S is low, X must select A0.
    check_select_low_routes_a0: assert property (
        @(posedge clk) !S |-> (X == A0)
    );

    // When S is high, X must select A1.
    check_select_high_routes_a1: assert property (
        @(posedge clk) S |-> (X == A1)
    );

    // If both data inputs are equal, X must equal that common value.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (A0 == A1) |-> (X == A0)
    );

    // With S low and A0 stable, X must remain stable.
    check_stable_when_select_low: assert property (
        @(posedge clk) (!S && $stable(S) && $stable(A0)) |-> $stable(X)
    );

    // With S high and A1 stable, X must remain stable.
    check_stable_when_select_high: assert property (
        @(posedge clk) (S && $stable(S) && $stable(A1)) |-> $stable(X)
    );

    // With S low and A0 changing, X must change.
    check_change_propagation_select_low: assert property (
        @(posedge clk) (!S && $stable(S) && $changed(A0)) |-> $changed(X)
    );

    // With S high and A1 changing, X must change.
    check_change_propagation_select_high: assert property (
        @(posedge clk) (S && $stable(S) && $changed(A1)) |-> $changed(X)
    );

    // With S low and A0 stable, a change on A1 must not affect X.
    check_unselected_input_ignored_select_low: assert property (
        @(posedge clk) (!S && $stable(S) && $stable(A0) && $changed(A1)) |-> $stable(X)
    );

    // With S high and A1 stable, a change on A0 must not affect X.
    check_unselected_input_ignored_select_high: assert property (
        @(posedge clk) (S && $stable(S) && $stable(A1) && $changed(A0)) |-> $stable(X)
    );

endmodule