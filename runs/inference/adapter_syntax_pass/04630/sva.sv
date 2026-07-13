module timer_sva #(
    parameter int res   = 33,
    parameter int phase = 12507
) (
    input logic             wb_clk_i,
    input logic             wb_rst_i,
    input logic             wb_tgc_o,
    input logic [res-1:0]   cnt,
    input logic             old_clk2,
    input logic             clk2
);

    // clk2 is the MSB of cnt.
    check_clk2_matches_cnt_msb: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        clk2 == cnt[res-1]
    );

    // old_clk2 captures the previous clk2 value.
    check_old_clk2_captures_clk2: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        1'b1 |=> (old_clk2 == $past(clk2))
    );

    // cnt increments by phase on each active cycle.
    check_cnt_increments_by_phase: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        1'b1 |=> (cnt == ($past(cnt) + phase))
    );

    // wb_tgc_o is asserted on the first clk2 rising edge after reset.
    check_wb_tgc_o_asserts_on_first_clk2_rise: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        1'b1 |=> ((wb_tgc_o == 1'b1) && ($past(old_clk2) == 1'b0) && (clk2 == 1'b1))
    );

    // wb_tgc_o is deasserted on the next clk2 falling edge.
    check_wb_tgc_o_deasserts_on_next_clk2_fall: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        1'b1 |=> ((wb_tgc_o == 1'b0) && ($past(old_clk2) == 1'b1) && (clk2 == 1'b0))
    );

    // wb_tgc_o is low on the first active cycle after reset.
    check_wb_tgc_o_low_after_reset: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        1'b1 |=> (wb_tgc_o == 1'b0)
    );

endmodule