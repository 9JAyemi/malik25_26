module synchronous_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);

    // Reset clears the counter to zero on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 4'd0)
    );

    // A count of nine rolls over to zero on the next clock.
    check_wrap_from_nine: assert property (
        @(posedge clk) (count == 4'd9) |=> (count == 4'd0)
    );

    // Any non-reset state other than nine increments by one.
    check_increment_otherwise: assert property (
        @(posedge clk) disable iff (rst)
        (count != 4'd9) |=> (count == ($past(count) + 4'd1))
    );

    // When not in reset, the counter value changes every clock.
    check_count_changes_without_reset: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (count != $past(count))
    );

endmodule