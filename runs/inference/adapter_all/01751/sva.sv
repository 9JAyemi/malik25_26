module c_clkgate_sva (
    input logic clk,
    input logic active,
    input logic clk_gated
);
    // clk_gated equals clk AND active_q at each clk edge.
    check_clk_gated_definition: assert property (
        @(posedge clk) clk_gated == (clk & $past(active))
    );

    // clk_gated is LOW whenever clk is LOW.
    check_clk_gated_low_when_clk_low: assert property (
        @(posedge clk) !clk |-> !clk_gated
    );

    // clk_gated can be HIGH only when clk is HIGH.
    check_clk_gated_implies_clk_high: assert property (
        @(posedge clk) clk_gated |-> clk
    );

    // clk_gated equals active_q at each clk edge.
    check_clk_gated_equals_active_q: assert property (
        @(posedge clk) clk_gated == $past(active)
    );

    // If active was 0 on the previous clk, clk_gated must be 0 now.
    check_prev_active_zero_forces_clk_gated_zero: assert property (
        @(posedge clk) !$past(active) |-> !clk_gated
    );

    // If active was 1 on the previous clk, clk_gated must be 1 now.
    check_prev_active_one_forces_clk_gated_one: assert property (
        @(posedge clk) $past(active) |-> clk_gated
    );

    // clk_gated can only rise when previous clk and active were both 1.
    check_clk_gated_rise_requires_prev_clk_active: assert property (
        @(posedge clk) $rose(clk_gated) |-> ($past(clk) && $past(active))
    );

    // clk_gated can only fall when previous clk was 0 or previous active was 0.
    check_clk_gated_fall_requires_prev_clk_inactive_or_active_zero: assert property (
        @(posedge clk) $fell(clk_gated) |-> (!$past(clk) || !$past(active))
    );

    // If clk_gated is 1 now, previous clk and active were both 1.
    check_clk_gated_one_implies_prev_clk_active: assert property (
        @(posedge clk) clk_gated |-> ($past(clk) && $past(active))
    );

    // If clk_gated is 0 now, previous clk was 0 or previous active was 0.
    check_clk_gated_zero_implies_prev_clk_inactive_or_active_zero: assert property (
        @(posedge clk) !clk_gated |-> (!$past(clk) || !$past(active))
    );
endmodule