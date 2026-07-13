module d_ff_en_ce_sva (
    input logic clk,
    input logic en,
    input logic enclk,
    input logic d,
    input logic q
);
    // Q updates with D on the next cycle when both enables are HIGH.
    update_on_enable: assert property (
        @(posedge clk) (en && enclk) |=> (q == $past(d))
    );

    // Q holds its value on the next cycle when at least one enable is LOW.
    hold_when_not_both: assert property (
        @(posedge clk) !(en && enclk) |=> (q == $past(q))
    );

    // Any change on Q must be due to both enables being HIGH in the previous cycle.
    change_requires_prev_enable: assert property (
        @(posedge clk) $changed(q) |-> $past(en && enclk)
    );

    // When Q changes, its new value equals the previous-cycle D.
    change_matches_prev_d: assert property (
        @(posedge clk) $changed(q) |-> (q == $past(d))
    );

    // If EN is LOW, Q must hold its previous value on the next cycle.
    hold_when_en_low: assert property (
        @(posedge clk) !en |=> (q == $past(q))
    );

    // If ENCLK is LOW, Q must hold its previous value on the next cycle.
    hold_when_enclk_low: assert property (
        @(posedge clk) !enclk |=> (q == $past(q))
    );

    // With both enables HIGH and D different from current Q, Q must change next cycle.
    enabled_and_data_diff_causes_change: assert property (
        @(posedge clk) (en && enclk && (d != q)) |=> (q != $past(q))
    );

    // With both enables HIGH and D equal to current Q, Q must not change next cycle.
    enabled_and_data_equal_causes_no_change: assert property (
        @(posedge clk) (en && enclk && (d == q)) |=> (q == $past(q))
    );

    // If both enables were HIGH but Q did not change, then D equaled Q in that cycle.
    no_change_under_enable_means_data_equal: assert property (
        @(posedge clk) ($past(en && enclk) && !$changed(q)) |-> ($past(d) == $past(q))
    );

    // Each cycle, Q equals either its previous value or the previous-cycle D.
    next_state_is_prev_q_or_prev_d: assert property (
        @(posedge clk) (q == $past(q)) || (q == $past(d))
    );
endmodule