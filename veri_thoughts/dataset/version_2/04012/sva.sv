module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);

    // Reset drives count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) !rst |-> (count == 4'b0000)
    );

    // A sampled reset cycle is followed by count still being zero on the next clock.
    check_reset_holds_count_zero: assert property (
        @(posedge clk) !rst |=> (count == 4'b0000)
    );

    // Outside reset, count increments by one every clock.
    check_count_increments: assert property (
        @(posedge clk) disable iff (!rst) 1'b1 |=> (count == ($past(count) + 4'd1))
    );

    // Count wraps from 4'hF back to 4'h0.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (!rst) (count == 4'hF) |=> (count == 4'h0)
    );

    // Count advances from zero to one when running.
    check_count_advances_from_zero: assert property (
        @(posedge clk) disable iff (!rst) (count == 4'h0) |=> (count == 4'h1)
    );

    // Any nonzero count value can only occur when reset is inactive.
    check_nonzero_count_requires_reset_inactive: assert property (
        @(posedge clk) (count != 4'b0000) |-> rst
    );

endmodule