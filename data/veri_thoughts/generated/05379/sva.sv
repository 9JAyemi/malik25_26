module fifo_read_counter_sva (
    input logic [11:0] out,
    input logic [11:0] O1,
    input logic sel,
    input logic rd_clk,
    input logic Q
);

    // Q clears both registers on the next sampled cycle.
    check_sync_clear: assert property (
        @(posedge rd_clk) disable iff (1'b0)
        Q |=> (out == 12'h000 && O1 == 12'h000)
    );

    // Q has priority over sel when both are high.
    check_clear_priority_over_sel: assert property (
        @(posedge rd_clk) disable iff (1'b0)
        (Q && sel) |=> (out == 12'h000 && O1 == 12'h000)
    );

    // sel increments out when Q is low.
    check_out_increments_on_sel: assert property (
        @(posedge rd_clk) disable iff (1'b0)
        (!Q && sel) |=> (out == ($past(out) + 12'd1))
    );

    // sel loads O1 with the previous out value when Q is low.
    check_o1_captures_previous_out: assert property (
        @(posedge rd_clk) disable iff (1'b0)
        (!Q && sel) |=> (O1 == $past(out))
    );

    // With Q low and sel low, both registers hold their values.
    check_hold_when_idle: assert property (
        @(posedge rd_clk) disable iff (1'b0)
        (!Q && !sel) |=> (out == $past(out) && O1 == $past(O1))
    );

    // After a sel update, out is exactly one count ahead of O1.
    check_sel_creates_expected_offset: assert property (
        @(posedge rd_clk) disable iff (1'b0)
        (!Q && sel) |=> (out == (O1 + 12'd1))
    );

endmodule