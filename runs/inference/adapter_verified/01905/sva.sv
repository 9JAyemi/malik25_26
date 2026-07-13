module simple_counter_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic [31:0] count
);

// Reset clears count to zero on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 32'd0)
    );

// When enabled outside reset, count increments by one.
    check_count_increments_when_enabled: assert property (
        @(posedge clk) disable iff (rst) en |=> (count == ($past(count) + 32'd1))
    );

// When not enabled outside reset, count holds its value.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (rst) !en |=> (count == $past(count))
    );

endmodule
