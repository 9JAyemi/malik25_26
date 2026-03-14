module dff_en_ce_sva (
    input logic clk,
    input logic en,
    input logic enclk,
    input logic d,
    input logic q
);
    // When both enables are HIGH, q updates to d on the next cycle.
    check_load_on_both_enables: assert property (
        @(posedge clk) (enclk && en) |=> (q == $past(d))
    );

    // When enclk is LOW, q holds its previous value.
    check_hold_when_enclk_low: assert property (
        @(posedge clk) (!enclk) |=> (q == $past(q))
    );

    // When enclk is HIGH but en is LOW, q holds its previous value.
    check_hold_when_en_low_but_enclk_high: assert property (
        @(posedge clk) (enclk && !en) |=> (q == $past(q))
    );

    // Any change on q must be caused by both enables being HIGH in the prior cycle.
    check_change_requires_prior_enable: assert property (
        @(posedge clk) $changed(q) |-> $past(enclk && en)
    );

    // If q changes, the new q equals the previous-cycle d.
    check_change_matches_prev_d: assert property (
        @(posedge clk) $changed(q) |-> (q == $past(d))
    );

    // Even if en is HIGH, if enclk is LOW, q must hold.
    check_hold_when_en_high_enclk_low: assert property (
        @(posedge clk) (en && !enclk) |=> (q == $past(q))
    );

    // If enabled and d equals current q, q must not change next cycle.
    check_no_toggle_when_enabled_and_equal_data: assert property (
        @(posedge clk) (enclk && en && (d == q)) |=> (q == $past(q))
    );

    // If enabled and d differs from current q, q must change next cycle.
    check_toggle_when_enabled_and_data_differs: assert property (
        @(posedge clk) (enclk && en && (d != q)) |=> $changed(q)
    );
endmodule