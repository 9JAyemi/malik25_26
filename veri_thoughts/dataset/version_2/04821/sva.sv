module flop_sync_rst_sva (
    input logic clk,
    input logic rst,
    input logic din,
    input logic q
);

    // Active-high synchronous reset clears q.
    check_sync_reset_clears_q: assert property (
        @(posedge clk) disable iff ($initstate)
        rst |=> (q == 1'b0)
    );

    // When reset is low, q captures din on the clock edge.
    check_flop_captures_din: assert property (
        @(posedge clk) disable iff ($initstate)
        !rst |=> (q == $past(din))
    );

    // q matches the previous cycle's reset-or-data selection.
    check_q_matches_previous_cycle_logic: assert property (
        @(posedge clk) disable iff ($initstate)
        q == ($past(rst) ? 1'b0 : $past(din))
    );

endmodule