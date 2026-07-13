module binary_counter_sva (
    input logic       clk,
    input logic       rst_n,
    input logic [3:0] count
);

    // Reset drives the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) !rst_n |-> (count == 4'b0000)
    );

    // The first sampled cycle after reset release still sees zero.
    check_reset_release_starts_from_zero: assert property (
        @(posedge clk) disable iff (!rst_n) (!$past(rst_n)) |-> (count == 4'b0000)
    );

    // The counter increments by one when the previous value was not 15.
    check_count_increments_no_rollover: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && ($past(count) != 4'hF)) |-> (count == ($past(count) + 4'd1))
    );

    // The counter wraps from 15 back to zero.
    check_count_rolls_over: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

endmodule