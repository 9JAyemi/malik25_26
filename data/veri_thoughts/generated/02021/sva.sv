module clock_gate_sva (
    input logic clk,
    input logic en,
    input logic te,
    input logic enclk
);
    // enclk must be LOW at each clk posedge (clk is LOW just before the edge).
    check_enclk_low_at_posedge: assert property (
        @(posedge clk) enclk == 1'b0
    );

    // During high phase, enclk equals en & te sampled at prior posedge.
    check_enclk_matches_latched_enable: assert property (
        @(negedge clk)
            ($past(1'b1, 1, posedge clk) == 1'b1)
            |-> (enclk == $past(en && te, 1, posedge clk))
    );

    // If en was LOW at posedge, enclk must be LOW this high phase.
    check_en_low_clears_enclk: assert property (
        @(negedge clk)
            ($past(1'b1, 1, posedge clk) == 1'b1) && ($past(en, 1, posedge clk) == 1'b0)
            |-> (enclk == 1'b0)
    );

    // If te was LOW at posedge, enclk must be LOW this high phase.
    check_te_low_clears_enclk: assert property (
        @(negedge clk)
            ($past(1'b1, 1, posedge clk) == 1'b1) && ($past(te, 1, posedge clk) == 1'b0)
            |-> (enclk == 1'b0)
    );

    // If both en and te were HIGH at posedge, enclk must be HIGH this high phase.
    check_both_high_sets_enclk: assert property (
        @(negedge clk)
            ($past(1'b1, 1, posedge clk) == 1'b1) && ($past(en && te, 1, posedge clk))
            |-> (enclk == 1'b1)
    );

    // A rising enclk at negedge implies en&te latched to 1 now and 0 previously.
    check_enclk_rise_cause: assert property (
        @(negedge clk)
            ($past(1'b1, 1, posedge clk) == 1'b1) && $rose(enclk)
            |-> ($past(en && te, 1, posedge clk) && !$past(en && te, 2, posedge clk))
    );

    // A falling enclk at negedge implies en&te latched to 0 now and 1 previously.
    check_enclk_fall_cause: assert property (
        @(negedge clk)
            ($past(1'b1, 1, posedge clk) == 1'b1) && $fell(enclk)
            |-> (!$past(en && te, 1, posedge clk) && $past(en && te, 2, posedge clk))
    );

    // If en&te were 1 for two consecutive posedges, enclk stays HIGH across two negedges.
    check_enclk_stays_high_when_enable_stays_high: assert property (
        @(negedge clk)
            ($past(1'b1, 1, posedge clk) == 1'b1) &&
            $past(en && te, 1, posedge clk) && $past(en && te, 2, posedge clk)
            |-> (enclk && $past(enclk))
    );

    // If en&te were 0 for two consecutive posedges, enclk stays LOW across two negedges.
    check_enclk_stays_low_when_enable_stays_low: assert property (
        @(negedge clk)
            ($past(1'b1, 1, posedge clk) == 1'b1) &&
            !$past(en && te, 1, posedge clk) && !$past(en && te, 2, posedge clk)
            |-> (!enclk && !$past(enclk))
    );
endmodule