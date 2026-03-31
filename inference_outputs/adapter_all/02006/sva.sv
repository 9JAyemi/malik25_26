module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count,
    input logic mux_out
);

    // Reset forces the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |-> (count == 4'b0000)
    );

    // Reset forces the mux output low.
    check_reset_clears_mux_out: assert property (
        @(posedge clk) rst |-> (mux_out == 1'b0)
    );

    // The counter increments by one on each clock.
    check_count_increments: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (count == ($past(count) + 4'b0001))
    );

    // The counter wraps from 15 back to 0.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (rst)
        (count == 4'b1111) |=> (count == 4'b0000)
    );

    // The mux output matches the LSB of the counter.
    check_mux_out_matches_lsb: assert property (
        @(posedge clk) disable iff (rst)
        (mux_out == count[0])
    );

    // The mux output is low when the counter is zero.
    check_mux_out_low_at_zero: assert property (
        @(posedge clk) disable iff (rst)
        (count == 4'b0000) |-> (mux_out == 1'b0)
    );

    // The mux output is high when the counter is one.
    check_mux_out_high_at_one: assert property (
        @(posedge clk) disable iff (rst)
        (count == 4'b0001) |-> (mux_out == 1'b1)
    );

    // The mux output is high when the counter is 15.
    check_mux_out_high_at_max: assert property (
        @(posedge clk) disable iff (rst)
        (count == 4'b1111) |-> (mux_out == 1'b1)
    );

endmodule