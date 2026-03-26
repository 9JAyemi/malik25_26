module constant_generator_sva (
    input logic [7:0] op,
    input logic       clk,
    input logic       ce,
    input logic       clr
);

    // Single-clock sequential logic with synchronous active-high clear.

    // A sampled clear forces op to zero on the following cycle.
    check_clear_drives_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(clr) |-> (op == 8'h00)
    );

    // With clear low, enable writes the constant 8'h01.
    check_enable_writes_one: assert property (
        @(posedge clk) disable iff ($initstate)
        $past((!clr) && ce) |-> (op == 8'h01)
    );

    // With both clear and enable low, op holds its previous value.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff ($initstate)
        $past((!clr) && (!ce)) |-> $stable(op)
    );

    // Clear has priority over enable when both are asserted.
    check_clear_priority_over_enable: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(clr && ce) |-> (op == 8'h00)
    );

    // op only changes after a clear or enable cycle.
    check_change_requires_write_condition: assert property (
        @(posedge clk) disable iff ($initstate)
        !$stable(op) |-> $past(clr || ce)
    );

endmodule