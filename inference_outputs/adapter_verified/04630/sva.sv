module timer_sva (
    input logic        wb_clk_i,
    input logic        wb_rst_i,
    input logic        wb_tgc_o,
    input logic [32:0] cnt,
    input logic        old_clk2
);

// Reset drives wb_tgc_o low on the next clock.
    check_reset_clears_tgc: assert property (
        @(posedge wb_clk_i) wb_rst_i |=> (wb_tgc_o == 1'b0)
    );

// wb_tgc_o is low whenever reset is asserted.
    check_tgc_low_during_reset: assert property (
        @(posedge wb_clk_i) wb_rst_i |-> (wb_tgc_o == 1'b0)
    );

// wb_tgc_o is high exactly when the previous two clocks had different parity.
    check_tgc_high_on_parity_change: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        ($past(!wb_rst_i) && $past(cnt[32]) != $past(cnt[31])) |-> (wb_tgc_o == 1'b1)
    );

// wb_tgc_o is low exactly when the previous two clocks had the same parity.
    check_tgc_low_on_parity_same: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        ($past(!wb_rst_i) && $past(cnt[32]) == $past(cnt[31])) |-> (wb_tgc_o == 1'b0)
    );

// A rising edge on wb_tgc_o implies the previous two clocks had different parity.
    check_tgc_rise_requires_parity_change: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        $rose(wb_tgc_o) |-> ($past(!wb_rst_i) && $past(cnt[32]) != $past(cnt[31]))
    );

// A falling edge on wb_tgc_o implies the previous two clocks had the same parity.
    check_tgc_fall_requires_parity_same: assert property (
        @(posedge wb_clk_i) disable iff (wb_rst_i)
        $fell(wb_tgc_o) |-> ($past(!wb_rst_i) && $past(cnt[32]) == $past(cnt[31]))
    );

endmodule
