module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);

    // Reset forces the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |-> (count == 4'h0)
    );

    // The counter increments by one on each non-reset clock.
    check_count_increments: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (count == ($past(count) + 4'h1))
    );

    // The counter wraps from 15 back to 0.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff (rst)
        (count == 4'hF) |=> (count == 4'h0)
    );

    // The least-significant bit toggles every non-reset clock.
    check_lsb_toggles: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (count[0] == ~$past(count[0]))
    );

    // The upper bits shift up by one on each non-reset clock.
    check_upper_bits_shift: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (count[3:1] == $past(count[2:0]))
    );

endmodule