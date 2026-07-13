module shift_register_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic shift,
    input logic [7:0] parallel_in,
    input logic [7:0] parallel_out
);
    // Clock: clk; Reset: reset (active-high, synchronous). Sequential regs with comb output.

    // On reset assertion, output becomes 0 on the next clock.
    reset_clears_output_next: assert property (
        @(posedge clk) reset |=> (parallel_out == 8'h00)
    );

    // On the cycle reset deasserts, output must be 0 (regs were cleared previous cycle).
    output_zero_on_reset_fall: assert property (
        @(posedge clk) $fell(reset) |-> (parallel_out == 8'h00)
    );

    // While reset is held across consecutive cycles, output remains 0.
    output_zero_while_reset_held: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (parallel_out == 8'h00)
    );

    // If previous cycle was not reset and enable was LOW, output holds its value.
    hold_when_prev_disable: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && !$past(enable)) |-> (parallel_out == $past(parallel_out))
    );

    // If enable is LOW in the current cycle, output holds into the next cycle.
    hold_next_when_disable_now: assert property (
        @(posedge clk) disable iff (reset) (!enable) |=> (parallel_out == $past(parallel_out))
    );

    // Any output change (with no prior reset) requires enable HIGH in the previous cycle.
    change_requires_prev_enable: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && (parallel_out != $past(parallel_out))) |-> $past(enable)
    );

    // If enable is LOW for two consecutive cycles, output is stable across both boundaries.
    stable_across_two_disable_cycles: assert property (
        @(posedge clk) disable iff (reset) (!enable ##1 !enable) |-> ($stable(parallel_out) ##1 $stable(parallel_out))
    );
endmodule