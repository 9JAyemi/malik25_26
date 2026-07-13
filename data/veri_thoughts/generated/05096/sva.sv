module mux_2to1_sva(
    input logic clk,
    input logic A0,
    input logic A1,
    input logic S,
    input logic X
);

    // When select is low, the output follows A0.
    check_select_low_routes_a0: assert property (
        @(posedge clk) (S === 1'b0) |-> (X === A0)
    );

    // When select is high, the output follows A1.
    check_select_high_routes_a1: assert property (
        @(posedge clk) (S === 1'b1) |-> (X === A1)
    );

    // With select held low, changes on A1 alone do not affect the output.
    check_a1_ignored_when_select_low: assert property (
        @(posedge clk)
        !$initstate &&
        (S === 1'b0) && ($past(S) === 1'b0) &&
        (A0 === $past(A0)) && (A1 !== $past(A1))
        |-> (X === $past(X))
    );

    // With select held high, changes on A0 alone do not affect the output.
    check_a0_ignored_when_select_high: assert property (
        @(posedge clk)
        !$initstate &&
        (S === 1'b1) && ($past(S) === 1'b1) &&
        (A1 === $past(A1)) && (A0 !== $past(A0))
        |-> (X === $past(X))
    );

    // A low-to-high select change switches the output to A1 when data inputs are stable.
    check_select_rise_routes_a1: assert property (
        @(posedge clk)
        !$initstate &&
        ($past(S) === 1'b0) && (S === 1'b1) &&
        (A0 === $past(A0)) && (A1 === $past(A1))
        |-> (X === A1)
    );

    // A high-to-low select change switches the output to A0 when data inputs are stable.
    check_select_fall_routes_a0: assert property (
        @(posedge clk)
        !$initstate &&
        ($past(S) === 1'b1) && (S === 1'b0) &&
        (A0 === $past(A0)) && (A1 === $past(A1))
        |-> (X === A0)
    );

    // With select held low, a change on A0 propagates to the output.
    check_a0_change_propagates_when_select_low: assert property (
        @(posedge clk)
        !$initstate &&
        (S === 1'b0) && ($past(S) === 1'b0) &&
        (A1 === $past(A1)) && (A0 !== $past(A0))
        |-> (X === A0) && (X !== $past(X))
    );

    // With select held high, a change on A1 propagates to the output.
    check_a1_change_propagates_when_select_high: assert property (
        @(posedge clk)
        !$initstate &&
        (S === 1'b1) && ($past(S) === 1'b1) &&
        (A0 === $past(A0)) && (A1 !== $past(A1))
        |-> (X === A1) && (X !== $past(X))
    );

endmodule