module up_counter_sva (
    input logic clk,
    input logic rst,
    input logic [2:0] count
);

    // Synchronous reset forces count to zero on the following clock.
    reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 3'b000)
    );

    // On consecutive non-reset cycles, count increments by one.
    count_advances_by_one: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (count == ($past(count) + 3'd1))
    );

    // The 3-bit counter wraps from 7 back to 0.
    count_wraps_from_max: assert property (
        @(posedge clk) disable iff (rst) (count == 3'b111) |=> (count == 3'b000)
    );

endmodule