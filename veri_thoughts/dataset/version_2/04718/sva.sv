module mux_1to2_async_rst_sva (
    input logic clk,
    input logic rst,
    input logic din0,
    input logic din1,
    input logic sel,
    input logic dout
);

    // Reset drives the registered output low.
    check_reset_forces_dout_low: assert property (
        @(posedge clk) rst |-> (dout == 1'b0)
    );

    // After a sampled reset cycle, the output remains low until the next clocked update.
    check_post_reset_dout_low: assert property (
        @(posedge clk) disable iff (rst)
        $past(rst) |-> (dout == 1'b0)
    );

    // With sel low, the output reflects the prior cycle's din0 value.
    check_sel0_updates_from_din0: assert property (
        @(posedge clk) disable iff (rst)
        $past(!rst && !sel) |-> (dout == $past(din0))
    );

    // With sel high, the output reflects the prior cycle's din1 value.
    check_sel1_updates_from_din1: assert property (
        @(posedge clk) disable iff (rst)
        $past(!rst && sel) |-> (dout == $past(din1))
    );

    // Outside reset, the output always matches the prior cycle's selected input.
    check_output_matches_previous_selected_input: assert property (
        @(posedge clk) disable iff (rst)
        $past(!rst) |-> (dout == ($past(sel) ? $past(din1) : $past(din0)))
    );

endmodule