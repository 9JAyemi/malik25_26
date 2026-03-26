module acc_sva (
    input logic clock,
    input logic reset,
    input logic clear,
    input logic enable_in,
    input logic enable_out,
    input logic signed [30:0] addend,
    input logic signed [33:0] sum
);

    // Reset drives sum to zero on the next cycle.
    check_sum_resets_to_zero: assert property (
        @(posedge clock) reset |=> (sum == 34'sd0)
    );

    // Clear loads the sign-extended addend into sum.
    check_sum_loads_addend_on_clear: assert property (
        @(posedge clock) disable iff (reset)
        clear |=> (sum == {{3{$past(addend[30])}}, $past(addend)})
    );

    // Enable accumulates addend into sum when clear is low.
    check_sum_accumulates_on_enable: assert property (
        @(posedge clock) disable iff (reset)
        (!clear && enable_in) |=> (sum == ($past(sum) + $past(addend)))
    );

    // Sum holds when reset, clear, and enable are all inactive.
    check_sum_holds_when_idle: assert property (
        @(posedge clock) disable iff (reset)
        (!clear && !enable_in) |=> (sum == $past(sum))
    );

    // Clear has priority over enable for sum updates.
    check_clear_priority_over_enable: assert property (
        @(posedge clock) disable iff (reset)
        (clear && enable_in) |=> (sum == {{3{$past(addend[30])}}, $past(addend)})
    );

    // Enable_out goes high one cycle after enable_in is high.
    check_enable_out_follows_enable_high: assert property (
        @(posedge clock) enable_in |=> enable_out
    );

    // Enable_out goes low one cycle after enable_in is low.
    check_enable_out_follows_enable_low: assert property (
        @(posedge clock) !enable_in |=> !enable_out
    );

endmodule