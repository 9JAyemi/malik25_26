module counter_display_sva (
    input logic clk,
    input logic reset,              // Synchronous active-high reset
    input logic direction,
    input logic [6:0] seg,
    input logic [3:0] cnt
);
    ///// Reset behavior /////
    // On a clock where reset is 1, cnt must be driven to 0.
    reset_clears_cnt: assert property (
        @(posedge clk) reset |-> (cnt == 4'b0000)
    );

    ///// Counter update rules /////
    // When not in reset and direction=1, cnt increments by 1 from the previous cycle.
    count_up_increments: assert property (
        @(posedge clk) disable iff (reset) direction |-> (cnt == $past(cnt) + 4'd1)
    );
    // When not in reset and direction=0, cnt decrements by 1 from the previous cycle.
    count_down_decrements: assert property (
        @(posedge clk) disable iff (reset) !direction |-> (cnt == $past(cnt) - 4'd1)
    );
    // When not in reset, cnt must change every cycle (no hold behavior).
    cnt_changes_every_cycle: assert property (
        @(posedge clk) disable iff (reset) cnt != $past(cnt)
    );

    ///// seg mapping /////
    // seg reflects {cnt[2:0], 4'b0000} due to splitter pass-through and width truncation.
    seg_exact_mapping: assert property (
        @(posedge clk) disable iff (reset) seg == {cnt[2:0], 4'b0000}
    );
    // Low nibble of seg is always zero.
    seg_low_nibble_zero: assert property (
        @(posedge clk) disable iff (reset) seg[3:0] == 4'b0000
    );
endmodule