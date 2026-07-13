module counter4_sva(
    input logic       clk,
    input logic       rst,
    input logic [3:0] count
);

    // When reset is high, count must be zero.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |-> (count == 4'd0)
    );

    // When count is 9, it wraps to 0 on the next clock if reset stays low.
    check_wrap_from_nine: assert property (
        @(posedge clk) disable iff (rst)
        (count == 4'd9) |=> (count == 4'd0)
    );

    // When count is not 9, it increments by 1 on the next clock if reset stays low.
    check_increment_when_not_nine: assert property (
        @(posedge clk) disable iff (rst)
        (count != 4'd9) |=> (count == ($past(count) + 4'd1))
    );

endmodule