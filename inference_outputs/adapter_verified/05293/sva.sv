module sync_counter_sva (
    input logic       clk,
    input logic       rst,
    input logic       load,
    input logic [3:0] data,
    input logic [3:0] count
);

// Reset drives count to zero on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 4'd0)
    );

// Load captures data into count on the next clock.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (rst)
        load |=> (count == $past(data))
    );

// Without load, count increments by one on the next clock.
    check_increment_when_not_loading: assert property (
        @(posedge clk) disable iff (rst)
        !load |=> (count == ($past(count) + 4'd1))
    );

// Increment wraps from 15 back to 0.
    check_increment_wraps_from_max: assert property (
        @(posedge clk) disable iff (rst)
        (!load && (count == 4'hF)) |=> (count == 4'h0)
    );

endmodule
