module timer_sva #(
    parameter int res   = 33,
    parameter int phase = 12507
) (
    input logic        wb_clk_i,
    input logic        wb_rst_i,
    input logic        wb_tgc_o,
    input logic [res-1:0] cnt,
    input logic        old_clk2,
    input logic        clk2
);

    // clk2 is the MSB of cnt.
    check_clk2_matches_cnt_msb: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        clk2 == cnt[res-1]
    );

    // wb_tgc_o is reset on the next cycle.
    check_tgc_reset_on_next_cycle: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        wb_tgc_o == 1'b0
    );

    // old_clk2 is reset on the next cycle.
    check_old_clk2_reset_on_next_cycle: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        old_clk2 == 1'b0
    );

    // wb_tgc_o is low after a reset cycle.
    check_tgc_low_after_reset_cycle: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        $past(wb_rst_i) |-> (wb_tgc_o == 1'b0)
    );

    // old_clk2 is low after a reset cycle.
    check_old_clk2_low_after_reset_cycle: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        $past(wb_rst_i) |-> (old_clk2 == 1'b0)
    );

    // clk2 is low after a reset cycle.
    check_clk2_low_after_reset_cycle: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        $past(wb_rst_i) |-> (clk2 == 1'b0)
    );

    // cnt is zero after a reset cycle.
    check_cnt_zero_after_reset_cycle: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        $past(wb_rst_i) |-> (cnt == '0)
    );

    // wb_tgc_o is high only when the prior cycle was a rising edge.
    check_tgc_high_only_on_rise: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        wb_tgc_o |-> $past(!old_clk2 && clk2)
    );

    // wb_tgc_o is high only when the prior cycle was not reset.
    check_tgc_high_only_when_not_reset: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        wb_tgc_o |-> !$past(wb_rst_i)
    );

    // A rising edge on clk2 sets old_clk2 high on the next cycle.
    check_old_clk2_set_on_clk2_rise: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        $rose(clk2) |=> old_clk2
    );

    // A falling edge on clk2 clears old_clk2 on the next cycle.
    check_old_clk2_clear_on_clk2_fall: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        $fell(clk2) |=> !old_clk2
    );

endmodule