module pipelined_counter_sva (
    input logic clk,
    input logic reset,       // Asynchronous active-high reset
    input logic [3:0] q
);
    // Helper: 4-bit increment with wrap at 0xF.
    function automatic logic [3:0] inc4(input logic [3:0] v);
        inc4 = (v == 4'hF) ? 4'h0 : (v + 4'h1);
    endfunction

    // During reset, q must be 0.
    reset_drives_zero: assert property (
        @(posedge clk) reset |-> (q == 4'h0)
    );

    // q equals +1 (mod 16) of the value 4 cycles earlier when no reset occurred in the past 4 cycles.
    increment_from_past4: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset,1) && !$past(reset,2) && !$past(reset,3) && !$past(reset,4))
            |-> (q == inc4($past(q,4)))
    );

    // Each active cycle, q either holds or increments by 1 (mod 16).
    hold_or_inc_each_cycle: assert property (
        @(posedge clk) disable iff (reset)
            1'b1 |-> (q == $past(q)) || (q == inc4($past(q)))
    );

    // If q changes this cycle, it must be the +1 (mod 16) of the previous value.
    change_implies_inc_of_prev: assert property (
        @(posedge clk) disable iff (reset)
            $changed(q) |-> (q == inc4($past(q)))
    );

    // After a change, q stays stable for the next 3 cycles.
    stable_three_after_change: assert property (
        @(posedge clk) disable iff (reset)
            $changed(q) |-> $stable(q)[*3]
    );

    // Changes occur exactly every 4 cycles (absent intervening reset).
    change_period_four: assert property (
        @(posedge clk) disable iff (reset)
            $changed(q) |-> ##4 $changed(q)
    );

    // After reset deassertion, q is 1 for the next 4 active cycles.
    post_reset_four_ones: assert property (
        @(posedge clk) disable iff (reset)
            $fell(reset) |-> (q == 4'h1) && (##1 q == 4'h1) && (##2 q == 4'h1) && (##3 q == 4'h1)
    );

    // If q is 0 and no reset in the last 4 cycles, 4-cycles-ago value was 15.
    wrap_only_from_15_past4: assert property (
        @(posedge clk) disable iff (reset)
            (q == 4'h0) && (!$past(reset,1) && !$past(reset,2) && !$past(reset,3) && !$past(reset,4))
            |-> ($past(q,4) == 4'hF)
    );

    // q is never X/Z while active.
    no_x_when_active: assert property (
        @(posedge clk) disable iff (reset)
            !$isunknown(q)
    );
endmodule