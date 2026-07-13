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

    // Core is asserted exactly when cnt_100M reaches 100,000,000.
    check_core_matches_100m_count: assert property (
        @(posedge slowest_sync_clk)
        Core == (cnt_100M == 32'd100000000)
    );

    // Core is a single-cycle pulse.
    check_core_is_single_cycle: assert property (
        @(posedge slowest_sync_clk)
        Core |=> !Core
    );

    // Core can only be high on the first cycle after cnt_100M wraps to zero.
    check_core_only_after_wrap: assert property (
        @(posedge slowest_sync_clk)
        Core |-> (cnt_100M == 32'd0)
    );

    // Core can only be high when the previous cycle's count was 99,999,999.
    check_core_only_after_99999999: assert property (
        @(posedge slowest_sync_clk)
        Core |-> ($past(cnt_100M) == 32'd99999999)
    );

    // Core is never high on consecutive cycles.
    check_core_not_back_to_back: assert property (
        @(posedge slowest_sync_clk)
        Core |=> !Core
    );

    // Core is never high when cnt_100M is zero.
    check_core_not_on_zero_count: assert property (
        @(posedge slowest_sync_clk)
        (cnt_100M == 32'd0) |-> !Core
    );

    // bsr is asserted exactly when cnt_core reaches 256.
    check_bsr_matches_core_count: assert property (
        @(posedge lpf_int)
        bsr == (cnt_core == 8'd256)
    );

    // pr is asserted exactly when cnt_bsr reaches 64.
    check_pr_matches_bsr_count: assert property (
        @(posedge lpf_int)
        pr == (cnt_bsr == 6'd64)
    );

    // pr is a single-cycle pulse.
    check_pr_is_single_cycle: assert property (
        @(posedge lpf_int)
        pr |=> !pr
    );

    // pr can only be high on the first cycle after cnt_bsr wraps to zero.
    check_pr_only_after_wrap: assert property (
        @(posedge lpf_int)
        pr |-> (cnt_bsr == 6'd0)
    );

    // pr can only be high when the previous cycle's count was 63.
    check_pr_only_after_63: assert property (
        @(posedge lpf_int)
        pr |-> ($past(cnt_bsr) == 6'd63)
    );

    // pr is never high on consecutive cycles.
    check_pr_not_back_to_back: assert property (
        @(posedge lpf_int)
        pr |=> !pr
    );

    // pr is never high when cnt_bsr is zero.
    check_pr_not_on_zero_count: assert property (
        @(posedge lpf_int)
        (cnt_bsr == 6'd0) |-> !pr
    );

endmodule