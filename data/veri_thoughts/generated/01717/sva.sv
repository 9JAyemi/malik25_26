module mux2_sva (
    input logic clk,
    input logic X,
    input logic A0,
    input logic A1,
    input logic S
);
    // X implements the 2:1 mux function X = S ? A1 : A0.
    check_mux_function: assert property (
        @(posedge clk) X === (S ? A1 : A0)
    );

    // When S is 0, X equals A0.
    check_select0_path: assert property (
        @(posedge clk) (S === 1'b0) |-> (X === A0)
    );

    // When S is 1, X equals A1.
    check_select1_path: assert property (
        @(posedge clk) (S === 1'b1) |-> (X === A1)
    );

    // If S==0 and S,A0 are stable, X remains stable.
    check_stability_selected_s0: assert property (
        @(posedge clk) (S === 1'b0 && $stable(S) && $stable(A0)) |-> $stable(X)
    );

    // If S==1 and S,A1 are stable, X remains stable.
    check_stability_selected_s1: assert property (
        @(posedge clk) (S === 1'b1 && $stable(S) && $stable(A1)) |-> $stable(X)
    );

    // If S==0 and stable, changes on unselected A1 do not affect X.
    check_unselected_a1_no_effect_s0: assert property (
        @(posedge clk) (S === 1'b0 && $stable(S) && $changed(A1)) |-> $stable(X)
    );

    // If S==1 and stable, changes on unselected A0 do not affect X.
    check_unselected_a0_no_effect_s1: assert property (
        @(posedge clk) (S === 1'b1 && $stable(S) && $changed(A0)) |-> $stable(X)
    );

    // With S==0 and stable, X can only change if A0 changes.
    check_x_change_cause_s0: assert property (
        @(posedge clk) (S === 1'b0 && $stable(S) && $changed(X)) |-> $changed(A0)
    );

    // With S==1 and stable, X can only change if A1 changes.
    check_x_change_cause_s1: assert property (
        @(posedge clk) (S === 1'b1 && $stable(S) && $changed(X)) |-> $changed(A1)
    );

    // If A0 equals A1, X must equal that common value.
    check_equal_inputs_dominance: assert property (
        @(posedge clk) (A0 === A1) |-> (X === A0)
    );
endmodule