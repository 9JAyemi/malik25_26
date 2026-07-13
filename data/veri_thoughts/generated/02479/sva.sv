module counter_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] q
);
    // When reset is HIGH at a clock edge, q is driven to 0.
    reset_forces_zero_at_clk: assert property (
        @(posedge clk) reset |-> (q == 4'h0)
    );

    // While reset remains HIGH across clock edges, q stays 0.
    reset_hold_zero_stable: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (q == 4'h0 && $past(q) == 4'h0)
    );

    // With reset LOW, q increments by 1 each clock (modulo 16).
    count_increments_by_one: assert property (
        @(posedge clk) disable iff (reset) q == $past(q) + 4'd1
    );

    // With reset LOW, q changes every cycle (no stutter).
    count_changes_each_cycle: assert property (
        @(posedge clk) disable iff (reset) q != $past(q)
    );

    // With reset LOW, wrap from 0xF to 0x0 on the next cycle.
    count_wraps_f_to_0: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset) && ($past(q) == 4'hF)) |-> (q == 4'h0)
    );

    // On the first clock after reset deasserts, q becomes 1.
    first_count_post_reset_is_one: assert property (
        @(posedge clk) disable iff (reset) $past(reset) |-> (q == 4'h1)
    );

    // With reset LOW, if q is 0 this cycle, previous q was 0xF.
    zero_implies_prev_f: assert property (
        @(posedge clk) disable iff (reset) (q == 4'h0) |-> ($past(q) == 4'hF)
    );

    // With reset LOW, if q is 1 this cycle, previous q was 0 or previous cycle was in reset.
    one_implies_prev_zero_or_reset: assert property (
        @(posedge clk) disable iff (reset) (q == 4'h1) |-> ($past(q) == 4'h0 || $past(reset))
    );
endmodule