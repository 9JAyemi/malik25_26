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

// Core is high exactly when cnt_100M reaches 100_000_000.
    check_core_high_when_cnt_100M_max: assert property (
        @(posedge slowest_sync_clk) disable iff (1'b0)
        (cnt_100M == 32'd100_000_000) |-> (Core == 1'b1)
    );

// Core is low when cnt_100M is not at 100_000_000.
    check_core_low_when_cnt_100M_not_max: assert property (
        @(posedge slowest_sync_clk) disable iff (1'b0)
        (cnt_100M != 32'd100_000_000) |-> (Core == 1'b0)
    );

// bsr is high exactly when Core is high and cnt_core reaches 255.
    check_bsr_high_when_core_and_cnt_core_max: assert property (
        @(posedge lpf_int) disable iff (1'b0)
        (Core && (cnt_core == 8'd255)) |-> (bsr == 1'b1)
    );

// bsr is low when Core is low or cnt_core is not at 255.
    check_bsr_low_when_core_low_or_cnt_core_not_max: assert property (
        @(posedge lpf_int) disable iff (1'b0)
        (!Core || (cnt_core != 8'd255)) |-> (bsr == 1'b0)
    );

// pr is high exactly when bsr is high and cnt_bsr reaches 63.
    check_pr_high_when_bsr_and_cnt_bsr_max: assert property (
        @(posedge lpf_int) disable iff (1'b0)
        (bsr && (cnt_bsr == 6'd63)) |-> (pr == 1'b1)
    );

// pr is low when bsr is low or cnt_bsr is not at 63.
    check_pr_low_when_bsr_low_or_cnt_bsr_not_max: assert property (
        @(posedge lpf_int) disable iff (1'b0)
        (!bsr || (cnt_bsr != 6'd63)) |-> (pr == 1'b0)
    );

endmodule
