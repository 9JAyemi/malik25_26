module comparator_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic       op,
    input logic       clk,
    input logic       ce,
    input logic       clr
);

    ///// Reset behavior /////
    // On clr assertion, op is cleared on the next clock.
    reset_clears_op_next: assert property (
        @(posedge clk) clr |=> (op == 1'b0)
    );

    // clr has priority over ce when both are asserted.
    reset_overrides_ce: assert property (
        @(posedge clk) (clr && ce) |=> (op == 1'b0)
    );

    ///// Capture behavior /////
    // With ce high, op updates next cycle to (a == b).
    update_on_ce: assert property (
        @(posedge clk) disable iff (clr) ce |=> (op == (a == b))
    );

    // With ce high and a == b, next op is 1.
    update_one_on_eq: assert property (
        @(posedge clk) disable iff (clr) (ce && (a == b)) |=> (op == 1'b1)
    );

    // With ce high and a != b, next op is 0.
    update_zero_on_neq: assert property (
        @(posedge clk) disable iff (clr) (ce && (a != b)) |=> (op == 1'b0)
    );

    ///// Hold behavior /////
    // With ce low, op holds its value unless reset occurs next cycle.
    hold_when_ce_low: assert property (
        @(posedge clk) disable iff (clr) (!ce) |=> (clr || $stable(op))
    );

    ///// Change qualification /////
    // A rising edge of op implies prior ce with a == b.
    op_rise_implies_prev_ce_eq: assert property (
        @(posedge clk) disable iff (clr) $rose(op) |-> $past(ce && (a == b))
    );

    // A falling edge of op implies prior ce with a != b or a prior reset.
    op_fall_implies_prev_ce_neq_or_reset: assert property (
        @(posedge clk) disable iff (clr) $fell(op) |-> ($past(ce && (a != b)) || $past(clr))
    );

endmodule