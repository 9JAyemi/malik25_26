module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic count_up,
    input logic [3:0] count
);
    // Reset drives count to zero at each clock.
    reset_forces_zero: assert property (
        @(posedge clk) reset |-> (count == 4'h0)
    );

    // While reset is held across cycles, count stays at 0 and stable.
    hold_zero_while_reset: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (count == 4'h0) && (count == $past(count))
    );

    // When counting up, next count is prev + 1 (mod 16).
    check_up_increments: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) && $past(count_up) |-> (count == $past(count) + 4'd1)
    );

    // When counting down, next count is prev - 1 (mod 16).
    check_down_decrements: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) && !$past(count_up) |-> (count == $past(count) - 4'd1)
    );

    // Up-wrap: from 0xF to 0 when count_up is 1.
    check_wrap_up: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) && $past(count_up) && ($past(count) == 4'hF) |-> (count == 4'h0)
    );

    // Down-wrap: from 0 to 0xF when count_up is 0.
    check_wrap_down: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) && !$past(count_up) && ($past(count) == 4'h0) |-> (count == 4'hF)
    );

    // If result is 0, prior state/direction must be F with up or 1 with down.
    check_zero_predecessors: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) && (count == 4'h0) |->
            ( ($past(count_up) && ($past(count) == 4'hF)) || (!$past(count_up) && ($past(count) == 4'h1)) )
    );

    // If result is F, prior state/direction must be E with up or 0 with down.
    check_f_predecessors: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) && (count == 4'hF) |->
            ( ($past(count_up) && ($past(count) == 4'hE)) || (!$past(count_up) && ($past(count) == 4'h0)) )
    );

    // Two-cycle up: +2 (mod 16) when count_up = 1 for two cycles.
    check_two_step_up: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset,2) && $past(!reset,1) && $past(count_up,2) && $past(count_up,1)
            |-> (count == $past(count,2) + 4'd2)
    );

    // Two-cycle down: -2 (mod 16) when count_up = 0 for two cycles.
    check_two_step_down: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset,2) && $past(!reset,1) && !$past(count_up,2) && !$past(count_up,1)
            |-> (count == $past(count,2) - 4'd2)
    );

    // LSB toggles on every active step (increment or decrement).
    check_lsb_toggles: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (count[0] == ~$past(count[0]))
    );
endmodule