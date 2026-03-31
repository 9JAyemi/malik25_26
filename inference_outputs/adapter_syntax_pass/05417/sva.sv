module counter_4bit_sync_reset_load_sva (
    input logic clk,
    input logic reset,
    input logic load,
    input logic [3:0] data_in,
    input logic [3:0] count
);

    // Reset clears the counter on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // Reset has priority over load when both are asserted.
    check_reset_priority_over_load: assert property (
        @(posedge clk) (reset && load) |=> (count == 4'b0000)
    );

    // Load updates the counter with data_in on the next clock.
    check_load_updates_count: assert property (
        @(posedge clk) disable iff (reset) load |=> (count == $past(data_in))
    );

    // Without load, the counter increments by one on the next clock.
    check_increment_when_no_load: assert property (
        @(posedge clk) disable iff (reset) !load |=> (count == ($past(count) + 4'd1))
    );

    // The counter wraps from 15 back to 0 when incrementing.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (reset) (!load && (count == 4'hF)) |=> (count == 4'h0)
    );

endmodule