module clock_gating_cell_sva (
    input logic clk,
    input logic enable,
    input logic gated_clk
);
    // gated_clk must be LOW when clk is HIGH (sampling at posedge).
    check_gclk_low_when_clk_high: assert property (
        @(posedge clk) gated_clk == 1'b0
    );

    // When clk is LOW (sampling at negedge), gated_clk equals enable.
    check_gclk_equals_enable_when_clk_low: assert property (
        @(negedge clk) gated_clk == enable
    );

    // If enable is stable across low phases, gated_clk is also stable.
    check_stability_when_enable_stable_low_phase: assert property (
        @(negedge clk) $stable(enable) |-> $stable(gated_clk)
    );
endmodule