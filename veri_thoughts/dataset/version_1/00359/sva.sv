module Freq_Count_Top_sva #(
    parameter int unsigned HIGH_TIME_Gate_1S = 50_000_000,
    parameter int unsigned LOW_TIME_Gate_1S  = 100_000_000
) (
    input logic        sys_clk_50m,
    input logic        ch_c,
    input logic        sys_rst_n,
    input logic [63:0] freq_reg,
    input logic        Gate_1S,
    input logic        Load,
    input logic        EN_FT,
    input logic        CLR,
    input logic [31:0] count,
    input logic [63:0] FT_out
);

    // Reset clears the sys_clk-domain counter and gate.
    reset_count_gate_state: assert property (
        @(posedge sys_clk_50m) !sys_rst_n |-> (count == 32'd0) && (Gate_1S == 1'b0)
    );

    // Count increments every sys_clk except at the programmed wrap point.
    count_increments_between_wraps: assert property (
        @(posedge sys_clk_50m) disable iff (!sys_rst_n)
        (count != LOW_TIME_Gate_1S) |=> (count == ($past(count) + 32'd1))
    );

    // Count reloads to 1 at the LOW_TIME terminal count.
    count_wraps_at_low_time: assert property (
        @(posedge sys_clk_50m) disable iff (!sys_rst_n)
        (count == LOW_TIME_Gate_1S) |=> (count == 32'd1)
    );

    // Gate_1S is driven low at the HIGH_TIME threshold.
    gate_clears_at_high_time: assert property (
        @(posedge sys_clk_50m) disable iff (!sys_rst_n)
        (count == HIGH_TIME_Gate_1S) |=> (Gate_1S == 1'b0)
    );

    // Gate_1S is driven high at the LOW_TIME threshold.
    gate_sets_at_low_time: assert property (
        @(posedge sys_clk_50m) disable iff (!sys_rst_n)
        (count == LOW_TIME_Gate_1S) |=> (Gate_1S == 1'b1)
    );

    // Gate_1S holds its value between the two terminal counts.
    gate_holds_between_thresholds: assert property (
        @(posedge sys_clk_50m) disable iff (!sys_rst_n)
        (count != HIGH_TIME_Gate_1S && count != LOW_TIME_Gate_1S) |=> (Gate_1S == $past(Gate_1S))
    );

    // Reset clears EN_FT in the ch_c domain.
    reset_clears_en_ft: assert property (
        @(posedge ch_c) !sys_rst_n |-> (EN_FT == 1'b0)
    );

    // EN_FT captures Gate_1S on each ch_c edge.
    en_ft_captures_gate: assert property (
        @(posedge ch_c) disable iff (!sys_rst_n)
        1'b1 |=> (EN_FT == $past(Gate_1S))
    );

    // Load is always the inverse of EN_FT.
    load_is_inverse_of_en_ft: assert property (
        @(posedge ch_c) disable iff (!sys_rst_n)
        (Load == !EN_FT)
    );

    // A high Gate_1S forces CLR high on the next ch_c cycle.
    gate_high_forces_clr_high: assert property (
        @(posedge ch_c) disable iff (!sys_rst_n)
        Gate_1S |=> (CLR == 1'b1)
    );

    // With both Gate_1S and EN_FT low, CLR is driven low next cycle.
    gate_and_enable_low_force_clr_low: assert property (
        @(posedge ch_c) disable iff (!sys_rst_n)
        (!Gate_1S && !EN_FT) |=> (CLR == 1'b0)
    );

    // A low CLR clears FT_out by the next ch_c sample.
    clr_low_clears_ft_out: assert property (
        @(posedge ch_c) disable iff (!sys_rst_n)
        (!CLR) |=> (FT_out == 64'd0)
    );

    // FT_out increments when counting is stably enabled.
    ft_out_increments_when_enabled: assert property (
        @(posedge ch_c) disable iff (!sys_rst_n)
        (CLR && Gate_1S && EN_FT) |=> (FT_out == ($past(FT_out) + 64'd1))
    );

    // freq_reg holds when the current ch_c edge cannot create a Load rise.
    freq_reg_stable_without_load_rise: assert property (
        @(posedge ch_c) disable iff (!sys_rst_n)
        !(EN_FT && !Gate_1S) |=> (freq_reg == $past(freq_reg))
    );

endmodule