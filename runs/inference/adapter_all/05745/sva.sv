module clk_gated_module_sva (
    input logic src_clk,
    input logic clk_en,
    input logic gated_clk
);
    // Clock: src_clk (posedge). No reset in RTL. Sequential gated_clk = clk_en_reg & src_clk.

    // gated_clk equals previous-cycle clk_en AND current src_clk.
    check_gated_clk_definition: assert property (
        @(posedge src_clk) gated_clk == $past(clk_en) && src_clk
    );

    // A high gated_clk requires previous clk_en was high.
    check_gated_high_requires_prev_en: assert property (
        @(posedge src_clk) gated_clk |-> $past(clk_en)
    );

    // A high gated_clk requires current src_clk is high.
    check_gated_high_requires_src_high: assert property (
        @(posedge src_clk) gated_clk |-> src_clk
    );

    // If previous clk_en was low, gated_clk must be low now.
    check_prev_en_low_forces_gated_low: assert property (
        @(posedge src_clk) !$past(clk_en) |-> !gated_clk
    );

    // If current src_clk is low, gated_clk must be low now.
    check_src_low_forces_gated_low: assert property (
        @(posedge src_clk) !src_clk |-> !gated_clk
    );

    // If previous clk_en was high, gated_clk equals current src_clk.
    check_prev_en_high_implies_gated_eq_src: assert property (
        @(posedge src_clk) $past(clk_en) |-> (gated_clk == src_clk)
    );

    // If current src_clk is high, gated_clk equals previous clk_en.
    check_src_high_implies_gated_eq_prev_en: assert property (
        @(posedge src_clk) src_clk |-> (gated_clk == $past(clk_en))
    );

    // If previous clk_en was high and current src_clk is high, gated_clk is high.
    check_prev_en_high_and_src_high_implies_gated_high: assert property (
        @(posedge src_clk) ($past(clk_en) && src_clk) |-> gated_clk
    );

    // If previous clk_en was low and current src_clk is high, gated_clk is low.
    check_prev_en_low_and_src_high_implies_gated_low: assert property (
        @(posedge src_clk) (!$past(clk_en) && src_clk) |-> !gated_clk
    );

    // If previous clk_en was high and current src_clk is low, gated_clk is low.
    check_prev_en_high_and_src_low_implies_gated_low: assert property (
        @(posedge src_clk) ($past(clk_en) && !src_clk) |-> !gated_clk
    );

endmodule