module sequence_counter_sva (
    input logic slowest_sync_clk,
    input logic lpf_int,
    input logic Core,
    input logic bsr,
    input logic pr,
    input logic [31:0] cnt_100M,
    input logic [7:0] cnt_core,
    input logic [5:0] cnt_bsr
);
    // Core reflects whether cnt_100M == 100_000_000.
    check_core_matches_cnt100m: assert property (
        @(posedge slowest_sync_clk) Core == (cnt_100M == 32'd100_000_000)
    );

    // bsr reflects whether cnt_core == 256.
    check_bsr_matches_cntcore: assert property (
        @(posedge lpf_int) bsr == (cnt_core == 8'd256)
    );

    // pr reflects whether cnt_bsr == 64.
    check_pr_matches_cntbsr: assert property (
        @(posedge lpf_int) pr == (cnt_bsr == 6'd64)
    );

    // pr can be HIGH only when bsr is HIGH.
    check_pr_implies_bsr: assert property (
        @(posedge lpf_int) pr |-> bsr
    );

    // pr can be HIGH only when Core is HIGH.
    check_pr_implies_core: assert property (
        @(posedge lpf_int) pr |-> Core
    );

    // bsr can be HIGH only when Core is HIGH.
    check_bsr_implies_core: assert property (
        @(posedge lpf_int) bsr |-> Core
    );

    // When Core is HIGH, bsr increments by 1 on the next lpf_int edge.
    check_bsr_increments_when_core_high: assert property (
        @(posedge lpf_int) Core |-> ##1 (bsr == ($past(bsr) + 1'b1))
    );

    // When Core is HIGH, pr increments by 1 on the next lpf_int edge.
    check_pr_increments_when_core_high: assert property (
        @(posedge lpf_int) Core |-> ##1 (pr == ($past(pr) + 1'b1))
    );

    // When bsr is HIGH, pr increments by 1 on the next lpf_int edge.
    check_pr_increments_when_bsr_high: assert property (
        @(posedge lpf_int) bsr |-> ##1 (pr == ($past(pr) + 1'b1))
    );

    // When Core is HIGH, cnt_core increments by 1 on the next lpf_int edge.
    check_cntcore_increments_when_core_high: assert property (
        @(posedge lpf_int) Core |-> ##1 (cnt_core == ($past(cnt_core) + 8'd1))
    );

    // When bsr is HIGH, cnt_bsr increments by 1 on the next lpf_int edge.
    check_cntbsr_increments_when_bsr_high: assert property (
        @(posedge lpf_int) bsr |-> ##1 (cnt_bsr == ($past(cnt_bsr) + 6'd1))
    );

    // When Core is HIGH, cnt_100M increments by 1 on the next slowest_sync_clk edge.
    check_cnt100m_increments_when_core_high: assert property (
        @(posedge slowest_sync_clk) Core |-> ##1 (cnt_100M == ($past(cnt_100M) + 32'd1))
    );

    // When Core is HIGH, Core is LOW on the next slowest_sync_clk edge.
    check_core_low_next_when_core_high: assert property (
        @(posedge slowest_sync_clk) Core |-> ##1 (Core == 1'b0)
    );

    // When bsr is HIGH, bsr is LOW on the next lpf_int edge.
    check_bsr_low_next_when_bsr_high: assert property (
        @(posedge lpf_int) bsr |-> ##1 (bsr == 1'b0)
    );

    // When pr is HIGH, pr is LOW on the next lpf_int edge.
    check_pr_low_next_when_pr_high: assert property (
        @(posedge lpf_int) pr |-> ##1 (pr == 1'b0)
    );
endmodule