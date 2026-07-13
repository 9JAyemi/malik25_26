module counter_sva (
    input logic clk,
    input logic rst,
    input logic [7:0] count
);

    // Reset forces count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |-> (count == 8'h00)
    );

    // Reset has priority over a previous count increment.
    check_reset_overrides_increment: assert property (
        @(posedge clk) (rst && $past(!rst)) |-> (count == 8'h00)
    );

    // Count increments by one when not in reset.
    check_count_increments: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |-> (count == ($past(count) + 8'd1))
    );

    // Count wraps from 8'hFF back to 8'h00.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (rst) (count == 8'hFF) |-> (count == 8'h00)
    );

endmodule