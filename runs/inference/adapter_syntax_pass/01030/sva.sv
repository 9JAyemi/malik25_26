module constant_generator_sva (
    input logic clk,
    input logic ce,
    input logic clr,
    input logic op
);

    // Clear forces the output low on the next clock.
    check_clear_forces_low: assert property (
        @(posedge clk) clr |=> (op == 1'b0)
    );

    // Clear has priority over clock enable when both are asserted.
    check_clear_priority_over_ce: assert property (
        @(posedge clk) (clr && ce) |=> (op == 1'b0)
    );

    // Clock enable sets the output high when clear is low.
    check_ce_sets_high: assert property (
        @(posedge clk) disable iff (clr) ce |=> (op == 1'b1)
    );

    // The output holds its value when neither clear nor clock enable is asserted.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (clr) (!ce) |=> (op == $past(op))
    );

endmodule