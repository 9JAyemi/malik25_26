module bitwise_operations_assertions (
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [1:0]  operation_select,
    input logic [4:0]  shift_amount,
    input logic [31:0] result
);

    // AND selection must drive the bitwise AND result.
    check_and_selected: assert property (
        @($global_clock) (operation_select == 2'b00) |-> (result == (a & b))
    );

    // OR selection must drive the bitwise OR result.
    check_or_selected: assert property (
        @($global_clock) (operation_select == 2'b01) |-> (result == (a | b))
    );

    // XOR selection must drive the bitwise XOR result.
    check_xor_selected: assert property (
        @($global_clock) (operation_select == 2'b10) |-> (result == (a ^ b))
    );

    // Shift selection must drive a left-shifted version of a.
    check_shift_selected: assert property (
        @($global_clock) (operation_select == 2'b11) |-> (result == (a << shift_amount))
    );

    // With all inputs unchanged, result must remain unchanged.
    check_no_state_when_inputs_stable: assert property (
        @($global_clock)
        (!$initstate &&
         (a == $past(a)) &&
         (b == $past(b)) &&
         (operation_select == $past(operation_select)) &&
         (shift_amount == $past(shift_amount)))
        |-> (result == $past(result))
    );

    // shift_amount must not affect result when shift is not selected.
    check_shift_amount_ignored_when_not_shift: assert property (
        @($global_clock)
        (!$initstate &&
         (operation_select == $past(operation_select)) &&
         (operation_select != 2'b11) &&
         (a == $past(a)) &&
         (b == $past(b)) &&
         (shift_amount != $past(shift_amount)))
        |-> (result == $past(result))
    );

    // b must not affect result when the shift operation is selected.
    check_b_ignored_during_shift: assert property (
        @($global_clock)
        (!$initstate &&
         (operation_select == 2'b11) &&
         ($past(operation_select) == 2'b11) &&
         (a == $past(a)) &&
         (shift_amount == $past(shift_amount)) &&
         (b != $past(b)))
        |-> (result == $past(result))
    );

endmodule