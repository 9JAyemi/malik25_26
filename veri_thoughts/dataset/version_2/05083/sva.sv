module mux2_sva (
    input logic clk,
    input logic X,
    input logic A0,
    input logic A1,
    input logic S
);

    // Exact mux equation sampled on the formal clock.
    check_mux_function: assert property (
        @(posedge clk) X === ((S == 1'b0) ? A0 : A1)
    );

    // Select low routes A0 to X.
    check_select_zero_routes_a0: assert property (
        @(posedge clk) (S === 1'b0) |-> (X === A0)
    );

    // Select high routes A1 to X.
    check_select_one_routes_a1: assert property (
        @(posedge clk) (S === 1'b1) |-> (X === A1)
    );

    // Equal data inputs force the same output value.
    check_equal_inputs_force_output: assert property (
        @(posedge clk) (A0 === A1) |-> (X === A0)
    );

    // A1 does not affect X while A0 is selected and stable.
    check_unselected_a1_has_no_effect: assert property (
        @(posedge clk) (S === 1'b0 && $stable(S) && $stable(A0) && $changed(A1)) |-> $stable(X)
    );

    // A0 does not affect X while A1 is selected and stable.
    check_unselected_a0_has_no_effect: assert property (
        @(posedge clk) (S === 1'b1 && $stable(S) && $stable(A1) && $changed(A0)) |-> $stable(X)
    );

endmodule