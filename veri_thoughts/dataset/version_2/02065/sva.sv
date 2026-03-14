module Freq_Divider_sva #(
    parameter int unsigned sys_clk = 50000000,
    parameter int unsigned clk_out = 1,
    parameter int unsigned max = sys_clk / (2*clk_out),
    parameter int unsigned N = $clog2(max)
) (
    input logic Clk_in,
    input logic Clk_out,
    input logic [N-1:0] counter
);
    // Clock: Clk_in (posedge). Reset: none.
    // Sequential counter; on max-1 -> counter=0 and Clk_out toggles; else counter++ and Clk_out holds.

    // When counter hits max-1, next cycle counter becomes 0.
    check_counter_resets_at_max: assert property (
        @(posedge Clk_in) (counter == max-1) |=> (counter == '0)
    );

    // When counter is not max-1, next cycle counter increments by 1.
    check_counter_increments_else: assert property (
        @(posedge Clk_in) (counter != max-1) |=> (counter == $past(counter) + 1'b1)
    );

    // When counter hits max-1, next cycle Clk_out toggles.
    check_clkout_toggles_at_max: assert property (
        @(posedge Clk_in) (counter == max-1) |=> (Clk_out == !$past(Clk_out))
    );

    // When counter is not max-1, next cycle Clk_out holds its value.
    check_clkout_holds_else: assert property (
        @(posedge Clk_in) (counter != max-1) |=> (Clk_out == $past(Clk_out))
    );

    // Any Clk_out change implies previous cycle counter was max-1.
    check_clkout_change_implies_prev_max: assert property (
        @(posedge Clk_in) $changed(Clk_out) |-> ($past(counter) == max-1)
    );

    // Any Clk_out change implies counter is 0 now.
    check_clkout_change_implies_counter_zero: assert property (
        @(posedge Clk_in) $changed(Clk_out) |-> (counter == '0)
    );

    // If Clk_out did not change, previous cycle counter was not max-1.
    check_no_change_implies_prev_not_max: assert property (
        @(posedge Clk_in) !$changed(Clk_out) |-> ($past(counter) != max-1)
    );

    // Counter updates every cycle (never holds its previous value).
    check_counter_always_updates: assert property (
        @(posedge Clk_in) 1'b1 |-> (counter != $past(counter))
    );

    // If counter is within range (< max), it remains within range next cycle.
    check_counter_range_invariant: assert property (
        @(posedge Clk_in) (counter < max) |=> (counter < max)
    );

    // No back-to-back Clk_out changes on consecutive cycles.
    check_no_back_to_back_clkout_change: assert property (
        @(posedge Clk_in) $changed(Clk_out) |=> !$changed(Clk_out)
    );
endmodule