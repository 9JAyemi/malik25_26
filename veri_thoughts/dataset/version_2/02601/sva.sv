module binary_counter_sva (
    input logic clk,
    input logic reset,      // active-high synchronous reset
    input logic enable,
    input logic [3:0] Q
);

    // Q must be 0 on any clock where reset is asserted.
    reset_clears_Q: assert property (
        @(posedge clk) reset |-> (Q == 4'b0000)
    );

    // When enable is LOW, Q holds its previous value.
    hold_when_enable_low: assert property (
        @(posedge clk) disable iff (reset) (!enable) |-> (Q == $past(Q))
    );

    // When enable is HIGH and previous Q != 15, Q increments by 1.
    increment_when_enable_high_no_wrap: assert property (
        @(posedge clk) disable iff (reset) (enable && ($past(Q) != 4'hF)) |-> (Q == $past(Q) + 4'd1)
    );

    // When enable is HIGH and previous Q == 15, Q wraps to 0.
    wrap_when_enable_high_from_fifteen: assert property (
        @(posedge clk) disable iff (reset) (enable && ($past(Q) == 4'hF)) |-> (Q == 4'h0)
    );

    // Q only changes on a clock when enable is HIGH (reset cycles disabled).
    change_requires_enable: assert property (
        @(posedge clk) disable iff (reset) $changed(Q) |-> enable
    );

    // If Q is 0 on a cycle with enable HIGH (and previous cycle not in reset), previous Q was 15.
    zero_with_enable_implies_prev_fifteen: assert property (
        @(posedge clk) disable iff (reset) (enable && (Q == 4'h0) && $past(!reset)) |-> ($past(Q) == 4'hF)
    );

    // Immediately after reset deasserts, if enable is HIGH, Q becomes 1.
    next_is_one_after_reset_then_enable: assert property (
        @(posedge clk) disable iff (reset) (!reset && $past(reset) && enable) |-> (Q == 4'd1)
    );

    // Immediately after reset deasserts, if enable is LOW, Q stays at 0.
    next_is_zero_after_reset_then_disable: assert property (
        @(posedge clk) disable iff (reset) (!reset && $past(reset) && !enable) |-> (Q == 4'd0)
    );

    // From previous Q == 15, next Q is either 0 if enable HIGH, or holds at 15 if enable LOW.
    next_from_fifteen_cases: assert property (
        @(posedge clk) disable iff (reset) ($past(Q) == 4'hF) |-> ((enable && (Q == 4'h0)) || (!enable && (Q == 4'hF)))
    );

    // When enabled and previous Q was 0, Q increments to 1.
    increment_from_zero_when_enabled: assert property (
        @(posedge clk) disable iff (reset) (enable && ($past(Q) == 4'h0)) |-> (Q == 4'h1)
    );

endmodule