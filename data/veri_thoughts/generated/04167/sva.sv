module up_counter_sva(
    input logic       clk,
    input logic       reset_n,
    input logic [3:0] count
);

    // When reset is active low, count must be zero.
    check_reset_forces_zero: assert property (
        @(posedge clk) !reset_n |-> (count == 4'h0)
    );

    // A non-maximum count increments by one on the next clock.
    check_count_increments_nonmax: assert property (
        @(posedge clk) disable iff (!reset_n)
        (count != 4'hF) |=> (count == ($past(count) + 4'd1))
    );

    // The counter wraps from 15 back to 0 on the next clock.
    check_count_wraps_at_max: assert property (
        @(posedge clk) disable iff (!reset_n)
        (count == 4'hF) |=> (count == 4'h0)
    );

    // After reset is released, the first counted value is 1.
    check_first_count_after_reset_release: assert property (
        @(posedge clk) disable iff (!reset_n)
        $rose(reset_n) |=> (count == 4'h1)
    );

endmodule