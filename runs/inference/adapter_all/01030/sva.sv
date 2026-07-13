module constant_generator_sva (
    input logic clk,
    input logic ce,
    input logic clr,
    input logic op
);
    // Clock: clk (posedge). Reset: clr (synchronous, active-high). Sequential flop with enable.

    // On clr, next cycle op must be 0.
    reset_clears_next: assert property (
        @(posedge clk) clr |=> (op == 1'b0)
    );

    // With ce high and clr low, next cycle op must be 1.
    enable_sets_next: assert property (
        @(posedge clk) disable iff (clr) ce |=> (op == 1'b1)
    );

    // With ce low and clr low, op holds its value.
    hold_when_ce_low: assert property (
        @(posedge clk) disable iff (clr) !ce |=> (op == $past(op))
    );

    // Any change in op must be caused by clr or ce.
    change_requires_enable_or_clear: assert property (
        @(posedge clk) disable iff (clr) (op != $past(op)) |-> ($past(clr) || $past(ce))
    );

    // If clr and ce are both high, clr has priority and next cycle op is 0.
    clear_priority_over_enable: assert property (
        @(posedge clk) (clr && ce) |=> (op == 1'b0)
    );

    // If ce is high and clr is low, next cycle op must be 1 regardless of prior value.
    enable_sets_next_irrespective_of_prev: assert property (
        @(posedge clk) disable iff (clr) ce |=> (op == 1'b1)
    );

    // If ce is high and clr is low, op must change next cycle.
    enable_changes_output: assert property (
        @(posedge clk) disable iff (clr) ce |=> (op != $past(op))
    );

    // If ce is low and clr is low, op must not change next cycle.
    hold_when_ce_low_no_change: assert property (
        @(posedge clk) disable iff (clr) !ce |=> (op == $past(op))
    );

    // If ce is high and clr is low, next cycle op must be 1 regardless of prior value.
    enable_sets_next_irrespective_of_prev: assert property (
        @(posedge clk) disable iff (clr) ce |=> (op == 1'b1)
    );

    // If ce is high and clr is low, op must change next cycle.
    enable_changes_output: assert property (
        @(posedge clk) disable iff (clr) ce |=> (op != $past(op))
    );

    // If ce is low and clr is low, op must not change next cycle.
    hold_when_ce_low_no_change: assert property (
        @(posedge clk) disable iff (clr) !ce |=> (op == $past(op))
    );
endmodule