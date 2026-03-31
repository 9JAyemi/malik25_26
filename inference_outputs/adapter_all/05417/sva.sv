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

    // Load captures data_in when reset is low.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (reset) load |=> (count == $past(data_in))
    );

    // Count increments by one when neither reset nor load is asserted.
    check_increment_when_idle: assert property (
        @(posedge clk) disable iff (reset) (!load) |=> (count == ($past(count) + 4'd1))
    );

    // The counter wraps from 15 back to 0 when incrementing.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (reset) (!load && (count == 4'hF)) |=> (count == 4'h0)
    );

endmodule