module up_down_counter_sva (
    input logic clk,
    input logic reset,    // synchronous active-high reset
    input logic Up,
    input logic Down,
    input logic [3:0] Q
);
    // Reset sets Q to zero on the next cycle.
    check_reset_clears_q_next: assert property (
        @(posedge clk) reset |=> (Q == 4'b0000)
    );

    // While reset stays asserted, Q remains zero.
    check_hold_zero_while_reset: assert property (
        @(posedge clk) ($past(reset) && reset) |-> (Q == 4'b0000)
    );

    // Increment by 1 when Up=1 and Down=0.
    check_inc_on_up_only: assert property (
        @(posedge clk) disable iff (reset) (Up && !Down) |=> (Q == $past(Q) + 1'b1)
    );

    // Decrement by 1 when Up=0 and Down=1.
    check_dec_on_down_only: assert property (
        @(posedge clk) disable iff (reset) (!Up && Down) |=> (Q == $past(Q) - 1'b1)
    );

    // Hold value when Up=0 and Down=0.
    check_hold_on_both_low: assert property (
        @(posedge clk) disable iff (reset) (!Up && !Down) |=> (Q == $past(Q))
    );

    // Hold value when Up=1 and Down=1.
    check_hold_on_both_high: assert property (
        @(posedge clk) disable iff (reset) (Up && Down) |=> (Q == $past(Q))
    );

    // Step size each cycle is 0, +1, or -1 (modulo 16) when not in reset.
    check_step_bounded_no_reset: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> ((Q == $past(Q)) || (Q == $past(Q) + 1'b1) || (Q == $past(Q) - 1'b1))
    );

    // A change in Q implies exactly one of Up/Down was asserted in the prior cycle.
    check_change_requires_one_hot_cmd: assert property (
        @(posedge clk) disable iff (reset) (Q != $past(Q)) |-> ($past(Up) ^ $past(Down))
    );

    // If Q increments by 1, the prior command must have been Up=1, Down=0.
    check_inc_implies_up_only: assert property (
        @(posedge clk) disable iff (reset) (Q == $past(Q) + 1'b1) |-> ($past(Up) && !$past(Down))
    );

    // If Q decrements by 1, the prior command must have been Up=0, Down=1.
    check_dec_implies_down_only: assert property (
        @(posedge clk) disable iff (reset) (Q == $past(Q) - 1'b1) |-> (!$past(Up) && $past(Down))
    );
endmodule