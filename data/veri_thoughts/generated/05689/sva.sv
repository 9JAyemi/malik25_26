module sky130_fd_sc_hs__mux2i_sva (
    input logic clk,
    input logic A0,
    input logic A1,
    input logic S,
    input logic VPWR,
    input logic VGND,
    input logic Y
);

    // When select is low, Y follows A0.
    check_select_low_routes_a0: assert property (
        @(posedge clk) disable iff (1'b0)
        (S === 1'b0) |-> (Y === A0)
    );

    // When select is high, Y follows A1.
    check_select_high_routes_a1: assert property (
        @(posedge clk) disable iff (1'b0)
        (S === 1'b1) |-> (Y === A1)
    );

    // With stable A0, A1, and S, Y stays stable.
    check_stable_inputs_hold_output: assert property (
        @(posedge clk) disable iff (1'b0)
        $stable({A0, A1, S}) |-> $stable(Y)
    );

    // While A0 remains selected and unchanged, A1 cannot affect Y.
    check_unselected_a1_is_ignored: assert property (
        @(posedge clk) disable iff (1'b0)
        (S === 1'b0 && $past(S) === 1'b0 && A0 === $past(A0)) |-> (Y === $past(Y))
    );

    // While A1 remains selected and unchanged, A0 cannot affect Y.
    check_unselected_a0_is_ignored: assert property (
        @(posedge clk) disable iff (1'b0)
        (S === 1'b1 && $past(S) === 1'b1 && A1 === $past(A1)) |-> (Y === $past(Y))
    );

endmodule