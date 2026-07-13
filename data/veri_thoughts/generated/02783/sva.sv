module counter_sva (
    input logic clk,
    input logic reset,
    input logic up_down,
    input logic load,
    input logic [3:0] load_data,
    input logic [3:0] count
);
    // Clock: clk (posedge). Reset: reset active-low (asynchronous). Sequential counter with load > up/down; wrap in 4 bits.

    // While reset is asserted, count must be 0.
    check_reset_forces_zero_now: assert property (
        @(posedge clk) !reset |-> (count == 4'd0)
    );

    // If reset is asserted, the next-cycle count remains 0.
    check_reset_holds_zero_next: assert property (
        @(posedge clk) !reset |=> (count == 4'd0)
    );

    // Load updates count with load_data on the next cycle.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (!reset) load |=> (count == $past(load_data))
    );

    // Load has priority over up_down when both are 1.
    check_load_overrides_updown: assert property (
        @(posedge clk) disable iff (!reset) (load && up_down) |=> (count == $past(load_data))
    );

    // When not loading and up_down=1, increment by 1.
    check_increment_when_up: assert property (
        @(posedge clk) disable iff (!reset) (!load && up_down) |=> (count == ($past(count) + 4'd1))
    );

    // When not loading and up_down=0, decrement by 1.
    check_decrement_when_down: assert property (
        @(posedge clk) disable iff (!reset) (!load && !up_down) |=> (count == ($past(count) - 4'd1))
    );

    // Next-state must be load_data, or +1, or -1 based on controls.
    check_next_state_matches_controls: assert property (
        @(posedge clk) disable iff (!reset)
            1'b1 |=> (
                ($past(load) && (count == $past(load_data))) ||
                (!$past(load) &&  $past(up_down) && (count == ($past(count) + 4'd1))) ||
                (!$past(load) && !$past(up_down) && (count == ($past(count) - 4'd1)))
            )
    );

    // Increment from 4'hF wraps to 4'h0 when not loading.
    check_increment_wraps_around: assert property (
        @(posedge clk) disable iff (!reset) (!load && up_down && (count == 4'hF)) |=> (count == 4'h0)
    );

    // Decrement from 4'h0 wraps to 4'hF when not loading.
    check_decrement_wraps_around: assert property (
        @(posedge clk) disable iff (!reset) (!load && !up_down && (count == 4'h0)) |=> (count == 4'hF)
    );

    // When not loading, count must change next cycle (no hold behavior).
    check_no_hold_without_load: assert property (
        @(posedge clk) disable iff (!reset) (!load) |=> (count != $past(count))
    );
endmodule