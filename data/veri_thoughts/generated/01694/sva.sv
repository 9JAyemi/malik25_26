module vco_interface_sva #(
    parameter int n = 8,
    parameter int unsigned fmin = 1000000,
    parameter int unsigned fmax = 2000000
)(
    input  logic              clk,
    input  logic              rst,
    input  logic [n-1:0]      vctrl,
    input  logic              vco_out,
    input  logic [31:0]       count,
    input  logic [31:0]       threshold
);
    localparam int unsigned TWO_TO_N = (1 << n);

    // During reset, count and vco_out are driven to 0.
    reset_state_is_zero: assert property (
        @(posedge clk) rst |-> (count == 32'd0) && (vco_out == 1'b0)
    );

    // Count update: increment by 1 unless at/over threshold, then reset to 0.
    count_update_rule: assert property (
        @(posedge clk) disable iff (rst)
            count == (($past(count) >= $past(threshold)) ? 32'd0 : ($past(count) + 32'd1))
    );

    // vco_out toggles only when previous count reached/exceeded threshold.
    vco_toggle_only_when_threshold_reached: assert property (
        @(posedge clk) disable iff (rst)
            (vco_out ^ $past(vco_out)) |-> ($past(count) >= $past(threshold))
    );

    // When previous count reached/exceeded threshold, vco_out must toggle.
    vco_toggle_on_threshold_reached: assert property (
        @(posedge clk) disable iff (rst)
            ($past(count) >= $past(threshold)) |-> (vco_out ^ $past(vco_out))
    );

    // When previous count was below threshold, vco_out must hold its value.
    vco_stable_when_below_threshold: assert property (
        @(posedge clk) disable iff (rst)
            ($past(count) < $past(threshold)) |-> (vco_out == $past(vco_out))
    );

    // A vco_out toggle coincides with count being reset to 0.
    toggle_implies_count_zero: assert property (
        @(posedge clk) disable iff (rst)
            (vco_out ^ $past(vco_out)) |-> (count == 32'd0)
    );

    // If not coming out of reset, count==0 implies previous count hit/exceeded threshold.
    count_zero_implies_previous_threshold_reached: assert property (
        @(posedge clk) disable iff (rst)
            (!$past(rst) && (count == 32'd0)) |-> ($past(count) >= $past(threshold))
    );

    // Threshold computation matches the RTL formula.
    threshold_computation_equation: assert property (
        @(posedge clk) disable iff (rst)
            threshold == (((fmax - fmin) * vctrl) / TWO_TO_N) + fmin
    );

    // Threshold is never below fmin.
    threshold_min_bound_fmin: assert property (
        @(posedge clk) disable iff (rst)
            threshold >= fmin
    );

    // Threshold is never above fmax.
    threshold_max_bound_fmax: assert property (
        @(posedge clk) disable iff (rst)
            threshold <= fmax
    );

    // Threshold is non-decreasing when vctrl increases.
    threshold_non_decreasing_with_vctrl: assert property (
        @(posedge clk) disable iff (rst)
            ($past(vctrl) < vctrl) |-> (threshold >= $past(threshold))
    );

    // Threshold holds constant when vctrl is unchanged.
    threshold_stable_when_vctrl_constant: assert property (
        @(posedge clk) disable iff (rst)
            (vctrl == $past(vctrl)) |-> (threshold == $past(threshold))
    );

endmodule