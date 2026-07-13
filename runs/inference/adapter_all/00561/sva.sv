module SimpleCalculator_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       op,
    input logic [3:0] result
);

    // Addition mode drives result to a + b.
    check_add_mode_result: assert property (
        @($global_clock) (op == 1'b0) |-> (result == (a + b))
    );

    // Subtraction mode drives result to a - b.
    check_sub_mode_result: assert property (
        @($global_clock) (op == 1'b1) |-> (result == (a - b))
    );

    // Stable inputs keep result stable.
    check_stable_inputs_hold_result: assert property (
        @($global_clock) ($stable(a) && $stable(b) && $stable(op)) |-> $stable(result)
    );

    // Changing only op selects the new operation.
    check_op_change_selects_operation: assert property (
        @($global_clock) ($changed(op) && $stable(a) && $stable(b)) |-> (result == (op ? (a - b) : (a + b)))
    );

    // Changing only a updates result to the selected operation.
    check_a_change_updates_result: assert property (
        @($global_clock) ($changed(a) && $stable(b) && $stable(op)) |-> (result == (op ? (a - b) : (a + b)))
    );

    // Changing only b updates result to the selected operation.
    check_b_change_updates_result: assert property (
        @($global_clock) ($changed(b) && $stable(a) && $stable(op)) |-> (result == (op ? (a - b) : (a + b)))
    );

endmodule