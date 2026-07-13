module up_down_counter_sva (
    input logic clk,
    input logic reset,
    input logic load,
    input logic up_down,
    input logic [3:0] count
);
    // Reset drives count to 0 on the clock edge while reset is asserted.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |-> (count == 4'h0)
    );

    // When load is asserted, the count holds its previous value.
    check_hold_on_load: assert property (
        @(posedge clk) disable iff (reset) load |-> (count == $past(count))
    );

    // When not loading and up_down=1, the count increments by 1.
    check_increment_on_up: assert property (
        @(posedge clk) disable iff (reset) (!load && up_down) |-> (count == $past(count) + 4'd1)
    );

    // When not loading and up_down=0, the count decrements by 1.
    check_decrement_on_down: assert property (
        @(posedge clk) disable iff (reset) (!load && !up_down) |-> (count == $past(count) - 4'd1)
    );

    // When not loading, the count must change each cycle.
    check_change_when_no_load: assert property (
        @(posedge clk) disable iff (reset) (!load) |-> (count != $past(count))
    );

    // Wrap from 0xF to 0x0 on increment when not loading.
    check_wrap_on_increment_from_max: assert property (
        @(posedge clk) disable iff (reset) (!load && up_down && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    // Wrap from 0x0 to 0xF on decrement when not loading.
    check_wrap_on_decrement_from_zero: assert property (
        @(posedge clk) disable iff (reset) (!load && !up_down && ($past(count) == 4'h0)) |-> (count == 4'hF)
    );

    // Two consecutive cycles of not loading and up count result in +2 net change.
    check_two_cycle_increment: assert property (
        @(posedge clk) disable iff (reset) (!load && up_down && $past(!load && up_down)) |-> (count == $past(count, 2) + 4'd2)
    );

    // Two consecutive cycles of not loading and down count result in -2 net change.
    check_two_cycle_decrement: assert property (
        @(posedge clk) disable iff (reset) (!load && !up_down && $past(!load && !up_down)) |-> (count == $past(count, 2) - 4'd2)
    );

    // If up_down toggles between cycles with no load, the two-cycle net change is 0.
    check_toggle_up_down_net_zero: assert property (
        @(posedge clk) disable iff (reset) (!load && $past(!load) && (up_down != $past(up_down))) |-> (count == $past(count, 2))
    );

    // Next-state is uniquely determined by load and up_down each cycle.
    check_deterministic_next_state: assert property (
        @(posedge clk) disable iff (reset)
            1'b1 |-> ( load ? (count == $past(count))
                           : (up_down ? (count == $past(count) + 4'd1)
                                      : (count == $past(count) - 4'd1)))
    );
endmodule