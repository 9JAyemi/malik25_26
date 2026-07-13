module clock_gate_sva (
    input logic clk,
    input logic en,
    input logic te,
    input logic enclk
);
    ///// Sequential update rules /////
    // When enabled, next enclk equals current te.
    capture_on_enable_next: assert property (
        @(posedge clk) en |=> (enclk == $past(te))
    );

    // When disabled, next enclk holds its previous value.
    hold_on_disable_next: assert property (
        @(posedge clk) !en |=> (enclk == $past(enclk))
    );

    ///// Next-state consistency using previous cycle /////
    // If en was 1 in the previous cycle, enclk equals previous te.
    prev_enable_updates: assert property (
        @(posedge clk) $past(en) |-> (enclk == $past(te))
    );

    // If en was 0 in the previous cycle, enclk equals its previous value.
    prev_disable_holds: assert property (
        @(posedge clk) !$past(en) |-> (enclk == $past(enclk))
    );

    ///// Change conditions /////
    // enclk can change only if previous en was 1 and previous te differed from previous enclk.
    change_requires_prior_enable_and_te_diff: assert property (
        @(posedge clk) (enclk != $past(enclk)) |-> ($past(en) && ($past(te) != $past(enclk)))
    );

    // If previous en was 1 and previous te equaled previous enclk, enclk must not change.
    no_change_when_prior_enable_and_te_same: assert property (
        @(posedge clk) ($past(en) && ($past(te) == $past(enclk))) |-> (enclk == $past(enclk))
    );

    ///// Steady follow behavior /////
    // With en high in consecutive cycles and te stable, enclk equals te.
    follow_when_en_and_te_stable: assert property (
        @(posedge clk) (en && $past(en) && (te == $past(te))) |-> (enclk == te)
    );

endmodule