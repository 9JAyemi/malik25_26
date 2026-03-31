module counter_4bit_sync_reset_load_sva (
    input logic       clk,
    input logic       reset,
    input logic       load,
    input logic [3:0] data_in,
    input logic [3:0] count
);

// Reset drives count to zero on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

// Load captures data_in when reset is low.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (reset) load |=> (count == $past(data_in))
    );

// Without load, count increments by one when reset is low.
    check_increment_when_not_load: assert property (
        @(posedge clk) disable iff (reset) !load |=> (count == ($past(count) + 4'd1))
    );

// Increment wraps from 15 back to 0 when reset is low.
    check_increment_wraps_from_max: assert property (
        @(posedge clk) disable iff (reset) (!load && (count == 4'hF)) |=> (count == 4'h0)
    );

endmodule
