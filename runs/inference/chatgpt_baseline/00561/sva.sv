module SimpleCalculator_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       op,
    input logic [3:0] result
);

    // Addition mode drives the sum of a and b.
    check_addition_result: assert property (
        @($global_clock) (op == 1'b0) |-> (result == (a + b))
    );

    // Subtraction mode drives the difference of a and b.
    check_subtraction_result: assert property (
        @($global_clock) (op == 1'b1) |-> (result == (a - b))
    );

    // Stable inputs keep the output stable.
    check_stable_inputs_hold_result: assert property (
        @($global_clock) (!$initstate && $stable({a, b, op})) |-> $stable(result)
    );

    // A rising op with stable operands selects subtraction.
    check_op_rise_selects_subtraction: assert property (
        @($global_clock) (!$initstate && $rose(op) && $stable({a, b})) |-> (result == (a - b))
    );

    // A falling op with stable operands selects addition.
    check_op_fall_selects_addition: assert property (
        @($global_clock) (!$initstate && $fell(op) && $stable({a, b})) |-> (result == (a + b))
    );

endmodule