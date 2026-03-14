module up_down_counter_sva (
    input logic clk,
    input logic reset,       // Active-low asynchronous reset
    input logic load,        // Active-low load
    input logic direction,   // 1: up, 0: down (when not loading)
    input logic [3:0] data_in,
    input logic [3:0] count
);
    // Reset low forces count to 0 at every sampled clock
    check_reset_low_forces_zero: assert property (
        @(posedge clk) (reset == 1'b0) |-> (count == 4'h0)
    );

    // While reset stays low across cycles, count stays at 0
    check_reset_hold_zero_stable: assert property (
        @(posedge clk) (!reset && $past(!reset)) |-> (count == 4'h0 && $past(count) == 4'h0)
    );

    // Load (active-low) captures data_in on next cycle
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (!reset)
            ($past(reset) && ($past(load) == 1'b0)) |-> (count == $past(data_in))
    );

    // With no load and direction==1, count increments by 1
    check_increment_when_dir1: assert property (
        @(posedge clk) disable iff (!reset)
            ($past(reset) && ($past(load) == 1'b1) && ($past(direction) == 1'b1)) |-> (count == $past(count) + 4'd1)
    );

    // With no load and direction==0, count decrements by 1
    check_decrement_when_dir0: assert property (
        @(posedge clk) disable iff (!reset)
            ($past(reset) && ($past(load) == 1'b1) && ($past(direction) == 1'b0)) |-> (count == $past(count) - 4'd1)
    );

    // Wrap-around on increment from 0xF to 0x0
    check_increment_wrap_from_F_to_0: assert property (
        @(posedge clk) disable iff (!reset)
            ($past(reset) && ($past(load) == 1'b1) && ($past(direction) == 1'b1) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    // Wrap-around on decrement from 0x0 to 0xF
    check_decrement_wrap_from_0_to_F: assert property (
        @(posedge clk) disable iff (!reset)
            ($past(reset) && ($past(load) == 1'b1) && ($past(direction) == 1'b0) && ($past(count) == 4'h0)) |-> (count == 4'hF)
    );

    // No-load update matches direction (+1 if 1, -1 if 0)
    check_no_load_update_matches_direction: assert property (
        @(posedge clk) disable iff (!reset)
            ($past(reset) && ($past(load) == 1'b1)) |-> (count == ($past(direction) ? ($past(count) + 4'd1) : ($past(count) - 4'd1)))
    );

    // Full next-state function: load has priority over counting
    check_full_next_state_function: assert property (
        @(posedge clk) disable iff (!reset)
            $past(reset) |-> (count ==
                (($past(load) == 1'b0) ? $past(data_in)
                                       : ($past(direction) ? ($past(count) + 4'd1)
                                                           : ($past(count) - 4'd1))))
    );

endmodule