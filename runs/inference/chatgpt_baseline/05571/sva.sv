module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] d1,
    input logic [7:0] d2,
    input logic [7:0] q,
    input logic [7:0] count
);

    // q clears to zero after a reset cycle.
    check_q_reset_zero: assert property (
        @(posedge clk) reset |=> (q == 8'd0)
    );

    // count clears to zero after a reset cycle.
    check_count_reset_zero: assert property (
        @(posedge clk) reset |=> (count == 8'd0)
    );

    // q captures d1+d2 on each active cycle.
    check_q_captures_sum: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (q == ($past(d1) + $past(d2)))
    );

    // count increments by one on each active cycle.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (count == ($past(count) + 8'd1))
    );

    // count wraps from 8'hff back to zero.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (reset)
        (count == 8'hff) |=> (count == 8'h00)
    );

endmodule