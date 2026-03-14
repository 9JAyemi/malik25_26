module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W48_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    // ENCLK rising edge must have had EN=1 and TE=0 in the previous cycle.
    check_enclk_rise_requires_prev_en1_te0: assert property (
        @(posedge CLK) disable iff (1'b0) $rose(ENCLK) |-> ($past(EN) == 1'b1 && $past(TE) == 1'b0)
    );

    // ENCLK rising edge implies enable condition was 0 two cycles ago (0->1 transition of EN&&!TE at t-2->t-1).
    check_enclk_rise_requires_prevprev_block: assert property (
        @(posedge CLK) disable iff (1'b0) $rose(ENCLK) |-> ($past(EN,2) == 1'b0 || $past(TE,2) == 1'b1)
    );

    // If previous cycle had EN=0 or TE=1, ENCLK cannot rise now.
    check_prev_cond_zero_blocks_enclk_rise: assert property (
        @(posedge CLK) disable iff (1'b0) (($past(EN) == 1'b0) || ($past(TE) == 1'b1)) |-> (!$rose(ENCLK))
    );

    // If the previous two cycles had EN=1 and TE=0, ENCLK cannot rise now.
    check_prev_two_cond_high_blocks_enclk_rise: assert property (
        @(posedge CLK) disable iff (1'b0)
        ($past(EN,1) == 1'b1 && $past(TE,1) == 1'b0 && $past(EN,2) == 1'b1 && $past(TE,2) == 1'b0)
        |-> (!$rose(ENCLK))
    );

    // No back-to-back ENCLK rising edges on consecutive cycles.
    check_no_back_to_back_enclk_rises: assert property (
        @(posedge CLK) disable iff (1'b0) $rose(ENCLK) |=> (!$rose(ENCLK))
    );

    // A rising TE forces ENCLK low by the next CLK edge.
    check_te_rise_clears_next: assert property (
        @(posedge CLK) disable iff (1'b0) $rose(TE) |=> (ENCLK == 1'b0)
    );

    // A rising TE prevents an ENCLK rise at the next CLK edge.
    check_te_rise_blocks_enclk_rise_next: assert property (
        @(posedge CLK) disable iff (1'b0) $rose(TE) |=> (!$rose(ENCLK))
    );

    // If TE rose last cycle, ENCLK cannot rise now.
    check_te_rose_last_cycle_blocks_enclk_rise: assert property (
        @(posedge CLK) disable iff (1'b0) ($past(TE,1) == 1'b1 && $past(TE,2) == 1'b0) |-> (!$rose(ENCLK))
    );

    // If TE is high now, ENCLK cannot rise on the next CLK edge.
    check_te_high_now_blocks_enclk_rise_next: assert property (
        @(posedge CLK) disable iff (1'b0) (TE == 1'b1) |=> (!$rose(ENCLK))
    );

    // ENCLK rising edge implies ENCLK is 1 in the same sampled cycle.
    check_enclk_rise_sets_one: assert property (
        @(posedge CLK) disable iff (1'b0) $rose(ENCLK) |-> (ENCLK == 1'b1)
    );
endmodule