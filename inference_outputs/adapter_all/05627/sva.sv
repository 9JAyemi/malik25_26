module counter4_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);

    // Reset forces count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |-> (count == 4'b0000)
    );

    // Count increments by one when not at 9.
    check_count_increments: assert property (
        @(posedge clk) disable iff (rst)
        (count != 4'b1001) |=> (count == ($past(count) + 4'b0001))
    );

    // Count wraps from 9 back to 0.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (rst)
        (count == 4'b1001) |=> (count == 4'b0000)
    );

    // Count never takes the invalid value 10.
    check_count_valid_range: assert property (
        @(posedge clk) disable iff (rst)
        (count != 4'b1010)
    );

endmodule