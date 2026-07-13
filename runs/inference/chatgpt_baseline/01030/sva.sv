module constant_generator_sva (
    input logic clk,
    input logic ce,
    input logic clr,
    input logic [(1 - 1):0] op
);
    ///// Reset behavior /////
    // Synchronous clear forces op low on the next cycle.
    reset_clears_op_next: assert property (
        @(posedge clk) clr |=> (op == 1'b0)
    );

    ///// Update and hold rules /////
    // With clr low, ce sets op high on the next cycle.
    ce_sets_op_high_next: assert property (
        @(posedge clk) disable iff (clr) ce |=> (op == 1'b1)
    );
    // With clr low and ce low, op holds its value.
    hold_without_ce: assert property (
        @(posedge clk) disable iff (clr) !ce |=> (op == $past(op))
    );
    // Once high and with clr low, op stays high.
    sticky_high_without_clr: assert property (
        @(posedge clk) disable iff (clr) (op == 1'b1) |=> (op == 1'b1)
    );

    ///// Transition causality /////
    // A rising edge on op only occurs if ce was 1 and clr was 0 in the prior cycle.
    rise_only_with_ce: assert property (
        @(posedge clk) disable iff (clr) $rose(op) |-> ($past(ce) && !$past(clr))
    );
    // A falling edge on op only occurs if clr was 1 in the prior cycle.
    fall_only_with_clr: assert property (
        @(posedge clk) $fell(op) |-> $past(clr)
    );
endmodule