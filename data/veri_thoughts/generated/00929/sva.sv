module up_down_counter_sva (
    input logic clk,
    input logic reset,       // active-high synchronous reset
    input logic load,
    input logic up_down,
    input logic [3:0] data_in,
    input logic [3:0] count_out
);
    ///// Reset behavior /////
    // Synchronous reset drives count_out to zero on the next clock.
    reset_clears_count: assert property (
        @(posedge clk) reset |=> (count_out == 4'b0000)
    );

    ///// Load behavior /////
    // When load is asserted (no reset), next count_out equals data_in.
    load_updates_count: assert property (
        @(posedge clk) disable iff (reset) load |=> (count_out == $past(data_in))
    );
    // Load has priority over up/down counting when both are asserted.
    load_overrides_updown: assert property (
        @(posedge clk) disable iff (reset) (load && up_down) |=> (count_out == $past(data_in))
    );

    ///// Counting behavior /////
    // When counting up (load=0, up_down=1), next count_out = previous + 1 (mod 16).
    count_up_when_up_down: assert property (
        @(posedge clk) disable iff (reset) (!load && up_down) |=> (count_out == ($past(count_out) + 4'd1))
    );
    // When counting down (load=0, up_down=0), next count_out = previous - 1 (mod 16).
    count_down_when_not_up_down: assert property (
        @(posedge clk) disable iff (reset) (!load && !up_down) |=> (count_out == ($past(count_out) - 4'd1))
    );

    ///// Wrap-around behavior /////
    // Up-count wraps from 15 to 0.
    wrap_on_increment_from_max: assert property (
        @(posedge clk) disable iff (reset) (!load && up_down && (count_out == 4'hF)) |=> (count_out == 4'h0)
    );
    // Down-count wraps from 0 to 15.
    wrap_on_decrement_from_min: assert property (
        @(posedge clk) disable iff (reset) (!load && !up_down && (count_out == 4'h0)) |=> (count_out == 4'hF)
    );
endmodule