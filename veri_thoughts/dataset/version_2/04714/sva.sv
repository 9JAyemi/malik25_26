module binary_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count
);

    // Clock: clk
    // Reset: reset is active low
    // Logic: sequential 4-bit up-counter

    // A low reset on a clock edge clears the counter.
    check_reset_clears_count: assert property (
        @(posedge clk) (!reset) |=> (count == 4'b0000)
    );

    // When reset is high, the counter increments by one each cycle.
    check_count_increments: assert property (
        @(posedge clk) disable iff (!reset) 1'b1 |=> (count == ($past(count) + 4'd1))
    );

    // The 4-bit counter wraps from 15 back to 0.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (!reset) (count == 4'hF) |=> (count == 4'h0)
    );

endmodule