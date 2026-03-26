module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] Q
);

    // Reset drives Q to zero.
    check_reset_clears_q: assert property (
        @(posedge clk) rst |=> (Q == 4'b0000)
    );

    // Q remains zero while reset stays asserted.
    check_q_zero_while_reset_held: assert property (
        @(posedge clk) disable iff ($initstate) (rst && $past(rst)) |-> (Q == 4'b0000)
    );

    // Q increments by one on each active cycle.
    check_q_increments: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (Q == ($past(Q) + 4'd1))
    );

    // Q wraps from 4'hF back to 4'h0.
    check_q_wraps: assert property (
        @(posedge clk) disable iff (rst) (Q == 4'hF) |=> (Q == 4'h0)
    );

    // The first count after reset release is 1.
    check_first_count_after_reset: assert property (
        @(posedge clk) disable iff ($initstate) (!rst && $past(rst)) |=> (Q == 4'h1)
    );

endmodule