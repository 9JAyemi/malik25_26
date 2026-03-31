module constant_generator_sva (
    input logic op,
    input logic clk,
    input logic ce,
    input logic clr
);

// Clear forces op low on the next clock.
    check_clear_forces_low: assert property (
        @(posedge clk) clr |=> (op == 1'b0)
    );

// Clear has priority over enable when both are asserted.
    check_clear_priority_over_enable: assert property (
        @(posedge clk) (clr && ce) |=> (op == 1'b0)
    );

// Enable sets op high on the next clock when clear is low.
    check_enable_sets_high: assert property (
        @(posedge clk) disable iff (clr) ce |=> (op == 1'b1)
    );

// Op holds its value when neither clear nor enable is asserted.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (clr) (!ce && !clr) |=> (op == $past(op))
    );

endmodule
