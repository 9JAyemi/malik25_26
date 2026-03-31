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

    // Pure combinational mux; sampled on an external clock with no RTL reset.

    // When S is high, X selects A1.
    check_select_high_routes_a1: assert property (
        @(posedge clk) disable iff (1'b0)
        (S === 1'b1) |-> (X === A1)
    );

    // When S is low, X selects A0.
    check_select_low_routes_a0: assert property (
        @(posedge clk) disable iff (1'b0)
        (S === 1'b0) |-> (X === A0)
    );

    // If both data inputs are equal, X matches that common value.
    check_equal_inputs_force_same_output: assert property (
        @(posedge clk) disable iff (1'b0)
        (A0 === A1) |-> (X === A0)
    );

    // If A0, A1, and S are stable, X remains stable.
    check_stable_inputs_hold_output: assert property (
        @(posedge clk) disable iff (1'b0)
        $stable({A0, A1, S}) |-> $stable(X)
    );

    // With S held low and A0 stable, changes on A1 do not affect X.
    check_unselected_a1_is_ignored: assert property (
        @(posedge clk) disable iff (1'b0)
        ((S === 1'b0) && $stable(S) && $stable(A0)) |-> $stable(X)
    );

    // With S held high and A1 stable, changes on A0 do not affect X.
    check_unselected_a0_is_ignored: assert property (
        @(posedge clk) disable iff (1'b0)
        ((S === 1'b1) && $stable(S) && $stable(A1)) |-> $stable(X)
    );

    // Power-pin changes do not affect X when mux inputs are unchanged.
    check_power_pins_do_not_affect_output: assert property (
        @(posedge clk) disable iff (1'b0)
        ($stable({A0, A1, S}) && !$stable({VPB, VPWR, VGND, VNB})) |-> $stable(X)
    );

endmodule