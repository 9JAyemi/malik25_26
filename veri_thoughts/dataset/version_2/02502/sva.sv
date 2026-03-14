module c_clkgate_sva (
    input logic clk,
    input logic enable,
    input logic clk_gated,
    input logic enable_q
);
    // Gated clock equals clk AND latched enable at both edges.
    check_clk_gated_is_and: assert property (
        @(posedge clk or negedge clk) clk_gated == (clk & enable_q)
    );

    // Gated clock is LOW whenever clk is LOW.
    check_gated_low_when_clk_low: assert property (
        @(negedge clk) clk_gated == 1'b0
    );

    // On clk rising edge, gated clock equals latched enable.
    check_posedge_reflects_latched_enable: assert property (
        @(posedge clk) clk_gated == enable_q
    );

    // At clk falling edge (latch open), latched enable updates to enable (after NBA).
    check_latch_transparent_when_clk_low: assert property (
        @(negedge clk) ##0 (enable_q == enable)
    );

    // Rising edges of gated clock only occur with clk rising edges.
    check_gated_rises_only_on_clk_rise: assert property (
        @(posedge clk or negedge clk) $rose(clk_gated) |-> $rose(clk)
    );

    // Falling edges of gated clock only occur with clk falling edges.
    check_gated_falls_only_on_clk_fall: assert property (
        @(posedge clk or negedge clk) $fell(clk_gated) |-> $fell(clk)
    );

    // Gated clock cannot be HIGH unless clk is HIGH.
    check_gated_implies_clk_high: assert property (
        @(posedge clk or negedge clk) clk_gated |-> clk
    );
endmodule