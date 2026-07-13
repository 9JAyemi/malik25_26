module sequence_counter_sva (
    input logic        slowest_sync_clk,
    input logic        lpf_int,
    input logic        Core,
    input logic        bsr,
    input logic        pr,
    input logic [31:0] cnt_100M,
    input logic [7:0]  cnt_core,
    input logic [5:0]  cnt_bsr
);

    // Terminal count resets cnt_100M and raises Core.
    check_core_pulse_on_terminal_count: assert property (
        @(posedge slowest_sync_clk)
        (cnt_100M == 32'd100_000_000) |=> (cnt_100M == 32'd0 && Core == 1'b1)
    );

    // Non-terminal count increments cnt_100M and keeps Core low.
    check_core_low_on_nonterminal_count: assert property (
        @(posedge slowest_sync_clk)
        (cnt_100M != 32'd100_000_000) |=> (cnt_100M == ($past(cnt_100M) + 32'd1) && Core == 1'b0)
    );

    // A sampled Core pulse corresponds to cnt_100M being reset.
    check_core_implies_zero_count: assert property (
        @(posedge slowest_sync_clk)
        (Core == 1'b1) |-> (cnt_100M == 32'd0)
    );

    // Core is a single slow-clock pulse.
    check_core_single_cycle_pulse: assert property (
        @(posedge slowest_sync_clk)
        (Core == 1'b1) |=> (Core == 1'b0)
    );

    // cnt_core increments when Core is sampled high.
    check_cnt_core_increments_when_core_high: assert property (
        @(posedge lpf_int)
        (Core == 1'b1) |=> (cnt_core == ($past(cnt_core) + 8'd1))
    );

    // cnt_core holds when Core is sampled low.
    check_cnt_core_holds_when_core_low: assert property (
        @(posedge lpf_int)
        (Core == 1'b0) |=> (cnt_core == $past(cnt_core))
    );

    // bsr is driven low after each lpf_int edge.
    check_bsr_clears_each_lpf_tick: assert property (
        @(posedge lpf_int)
        1'b1 |=> (bsr == 1'b0)
    );

    // cnt_bsr increments when bsr is sampled high.
    check_cnt_bsr_increments_when_bsr_high: assert property (
        @(posedge lpf_int)
        (bsr == 1'b1) |=> (cnt_bsr == ($past(cnt_bsr) + 6'd1) && pr == 1'b0)
    );

    // cnt_bsr holds when bsr is sampled low.
    check_cnt_bsr_holds_when_bsr_low: assert property (
        @(posedge lpf_int)
        (bsr == 1'b0) |=> (cnt_bsr == $past(cnt_bsr))
    );

    // pr is driven low after each lpf_int edge.
    check_pr_clears_each_lpf_tick: assert property (
        @(posedge lpf_int)
        1'b1 |=> (pr == 1'b0)
    );

endmodule

bind sequence_counter sequence_counter_sva sequence_counter_sva_inst (
    .slowest_sync_clk(slowest_sync_clk),
    .lpf_int(lpf_int),
    .Core(Core),
    .bsr(bsr),
    .pr(pr),
    .cnt_100M(cnt_100M),
    .cnt_core(cnt_core),
    .cnt_bsr(cnt_bsr)
);