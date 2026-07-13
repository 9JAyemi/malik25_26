module relational_module_assertions (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic       op,
    input logic       clk,
    input logic       ce,
    input logic       clr
);

    // clk is the only clock; clr is active-high and resets only the staged a/b registers.
    // op is sequential and updates only on enabled clock edges.

    // When ce is low, op is not updated and must hold its value.
    check_op_holds_when_ce_low: assert property (
        @(posedge clk) disable iff (clr)
        !ce |=> (op === $past(op))
    );

    // Any observed change on op must come from an enabled update on the prior clock.
    check_op_changes_only_after_enabled_cycle: assert property (
        @(posedge clk) disable iff (clr)
        (!$initstate && (op !== $past(op))) |-> $past(ce)
    );

    // After a sampled reset cycle, the next enabled compare must see 0 == 0 and drive op high.
    check_first_enabled_compare_after_reset_is_true: assert property (
        @(posedge clk) disable iff (clr)
        (!$initstate && $past(clr) && ce) |=> (op === 1'b1)
    );

endmodule