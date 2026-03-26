module counter_sva (
    input logic       clk,
    input logic [3:0] count
);

    // Count increments by one when it is below 15.
    check_count_increments_until_max: assert property (
        @(posedge clk)
        (count != 4'd15) |=> (count == ($past(count) + 4'd1))
    );

    // Count wraps to 0 after reaching 15.
    check_count_wraps_after_max: assert property (
        @(posedge clk)
        (count == 4'd15) |=> (count == 4'd0)
    );

endmodule