module decade_counter_sva (
    input logic       clk,
    input logic       reset_n,
    input logic [3:0] count
);

    // A sampled low reset forces the count to zero by the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) (!reset_n) |=> (count == 4'd0)
    );

    // On the sampled release of reset, the count is still zero.
    check_zero_on_reset_release: assert property (
        @(posedge clk) disable iff (!reset_n)
        $rose(reset_n) |-> (count == 4'd0)
    );

    // Counts below nine increment by one on the next clock.
    check_increment_when_below_nine: assert property (
        @(posedge clk) disable iff (!reset_n)
        (count < 4'd9) |=> (count == ($past(count) + 4'd1))
    );

    // A count of nine wraps back to zero on the next clock.
    check_wrap_when_nine: assert property (
        @(posedge clk) disable iff (!reset_n)
        (count == 4'd9) |=> (count == 4'd0)
    );

    // During normal operation, the count stays in the 0 to 9 range.
    check_count_in_decade_range: assert property (
        @(posedge clk) disable iff (!reset_n)
        (count <= 4'd9)
    );

endmodule