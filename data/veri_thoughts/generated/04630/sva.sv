module timer_sva #(
    parameter res   = 33,
    parameter phase = 12507
) (
    input  logic             wb_clk_i,
    input  logic             wb_rst_i,
    input  logic             wb_tgc_o,
    input  logic [res-1:0]   cnt,
    input  logic             old_clk2,
    input  logic             clk2
);

    localparam [res-1:0] PHASE_VAL = phase;

    // clk2 is always the MSB of cnt.
    check_clk2_matches_cnt_msb: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        (clk2 == cnt[res-1])
    );

    // A reset cycle clears the sequential state on the following cycle.
    check_reset_clears_state: assert property (
        @(posedge wb_clk_i)
        wb_rst_i |=> ((cnt == '0) && (old_clk2 == 1'b0) && (wb_tgc_o == 1'b0) && (clk2 == 1'b0))
    );

    // When not reset, cnt advances by phase each clock.
    check_cnt_advances_by_phase: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        1'b1 |=> (cnt == ($past(cnt) + PHASE_VAL))
    );

    // old_clk2 captures the prior sampled value of clk2.
    check_old_clk2_tracks_clk2: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        1'b1 |=> (old_clk2 == $past(clk2))
    );

    // wb_tgc_o is the registered rising-edge detect of clk2.
    check_wb_tgc_edge_detect: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        1'b1 |=> (wb_tgc_o == ((!$past(old_clk2)) & $past(clk2)))
    );

    // A high wb_tgc_o means old_clk2 has just risen.
    check_wb_tgc_implies_old_clk2_rise: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        (!$initstate && wb_tgc_o) |-> (old_clk2 && !$past(old_clk2))
    );

    // wb_tgc_o is a one-cycle pulse.
    check_wb_tgc_single_cycle: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        wb_tgc_o |=> !wb_tgc_o
    );

endmodule