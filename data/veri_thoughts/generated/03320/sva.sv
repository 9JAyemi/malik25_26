module dff_sync_rst_sva (
    input logic clk,
    input logic rst,
    input logic d,
    input logic q
);

    // A reset clock edge must leave q low on the next sampled cycle.
    check_reset_clears_q: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        $past(rst) |-> (q == 1'b0)
    );

    // A non-reset clock edge with d high must be captured into q.
    check_capture_one: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && $past(d)) |-> (q == 1'b1)
    );

    // A non-reset clock edge with d low must be captured into q.
    check_capture_zero: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && !$past(d)) |-> (q == 1'b0)
    );

endmodule