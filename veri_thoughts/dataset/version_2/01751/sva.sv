module c_clkgate_sva (
    input logic clk,
    input logic active,
    input logic clk_gated,
    input logic active_q
);
    // Clock: clk. No reset. Sequential (latch-based) gating: active latched to active_q when clk==0; clk_gated = clk & active_q.

    // Gated clock must be LOW whenever clk is LOW.
    check_gated_low_when_clk_low: assert property (
        @(negedge clk) clk_gated == 1'b0
    );

    // On clk rising edge, gated clock equals the latched enable.
    check_gated_equals_latch_on_posedge: assert property (
        @(posedge clk) clk_gated == active_q
    );

    // Latched enable is stable during clk HIGH phase (from posedge to next negedge).
    check_latch_stable_during_high: assert property (
        @(negedge clk) active_q == $past(active_q, 1, posedge clk)
    );

    // A rising edge on gated clock across posedges matches a rising edge on the latched enable.
    check_gated_rise_matches_latch_rise: assert property (
        @(posedge clk) $rose(clk_gated) |-> $rose(active_q)
    );

    // A falling edge on gated clock across posedges matches a falling edge on the latched enable.
    check_gated_fall_matches_latch_fall: assert property (
        @(posedge clk) $fell(clk_gated) |-> $fell(active_q)
    );

endmodule