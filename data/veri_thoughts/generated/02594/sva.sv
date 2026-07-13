module counter_4bit_with_async_reset_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] Q
);
    // While reset is HIGH at a clock edge, Q must be 0.
    reset_value_now: assert property (
        @(posedge clk) reset |-> (Q == 4'd0)
    );

    // If reset is HIGH at a clock edge, Q is 0 at the next clock edge too.
    reset_zero_next_cycle: assert property (
        @(posedge clk) reset |-> ##1 (Q == 4'd0)
    );

    // When the previous cycle was not in reset, Q increments by 1 (mod 16).
    increment_when_prev_not_reset: assert property (
        @(posedge clk) disable iff ($initstate)
            (!$past(reset)) |-> (Q == $past(Q) + 4'd1)
    );

    // Explicit wrap: from 15 to 0 when previous cycle was not in reset.
    wrap_from_15_to_0: assert property (
        @(posedge clk) disable iff ($initstate)
            (!$past(reset) && ($past(Q) == 4'd15)) |-> (Q == 4'd0)
    );

    // If not in reset previously and Q is 0 now, previous Q must have been 15 (wrap cause).
    zero_only_from_wrap_when_prev_not_reset: assert property (
        @(posedge clk) disable iff ($initstate)
            (!$past(reset) && (Q == 4'd0)) |-> ($past(Q) == 4'd15)
    );

    // Q is stable across consecutive cycles while reset is held HIGH.
    q_stable_while_reset_held: assert property (
        @(posedge clk) disable iff ($initstate)
            ($past(reset) && reset) |-> (Q == $past(Q))
    );
endmodule