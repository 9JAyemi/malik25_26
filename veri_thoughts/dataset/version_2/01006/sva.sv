module counter_sva (
    input logic Clk,
    input logic Reset,     // Active-high synchronous reset
    input logic Enable,
    input logic [3:0] Q
);
    ///// Counter behavior (sequential, posedge Clk) /////
    // On reset, Q is driven to 0 in the same cycle.
    reset_forces_zero: assert property (
        @(posedge Clk) Reset |-> (Q == 4'h0)
    );

    // Reset has priority over Enable.
    reset_priority_over_enable: assert property (
        @(posedge Clk) Reset && Enable |-> (Q == 4'h0)
    );

    // When not in reset and Enable is LOW, Q holds its value.
    hold_when_disabled: assert property (
        @(posedge Clk) disable iff (Reset) (!Enable) |-> (Q == $past(Q))
    );

    // When not in reset and Enable is HIGH, Q increments by 1 (mod 16).
    increment_when_enabled: assert property (
        @(posedge Clk) disable iff (Reset) (Enable) |-> (Q == ($past(Q) + 4'd1))
    );

    // When not in reset, if previous Q was 0xF and Enable is HIGH, Q wraps to 0.
    wrap_on_max: assert property (
        @(posedge Clk) disable iff (Reset) (Enable && ($past(Q) == 4'hF)) |-> (Q == 4'h0)
    );

    // With Enable HIGH for two consecutive cycles (and previous cycle not in reset), Q advances by 2.
    two_cycle_increment: assert property (
        @(posedge Clk) disable iff (Reset) (Enable && $past(Enable) && !$past(Reset)) |-> (Q == ($past(Q,2) + 4'd2))
    );

    // With Enable LOW for two consecutive cycles (and previous cycle not in reset), Q holds over two cycles.
    two_cycle_hold: assert property (
        @(posedge Clk) disable iff (Reset) (!Enable && !$past(Enable) && !$past(Reset)) |-> (Q == $past(Q,2))
    );

    // While reset is held across cycles, Q remains 0.
    reset_held_keeps_zero: assert property (
        @(posedge Clk) (Reset && $past(Reset)) |-> (Q == 4'h0 && $past(Q) == 4'h0)
    );
endmodule