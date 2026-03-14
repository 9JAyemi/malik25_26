module simple_arithmetic_unit_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [1:0] op_select,
    input logic [3:0] result,
    input logic       carry_borrow
);
    // When op_select=00, outputs equal 5-bit addition of a and b.
    check_add_operation: assert property (
        @($global_clock) (op_select == 2'b00) |-> ({carry_borrow, result} == (a + b))
    );

    // When op_select=01, outputs equal 5-bit subtraction of a and b.
    check_sub_operation: assert property (
        @($global_clock) (op_select == 2'b01) |-> ({carry_borrow, result} == (a - b))
    );

    // For subtraction, borrow flag is 1 iff a < b.
    check_sub_borrow_flag: assert property (
        @($global_clock) (op_select == 2'b01) |-> (carry_borrow == (a < b))
    );

    // When op_select=10, result is a & b and carry_borrow is 0.
    check_and_operation: assert property (
        @($global_clock) (op_select == 2'b10) |-> (result == (a & b)) && (carry_borrow == 1'b0)
    );

    // When op_select=11 (default), outputs are zero.
    check_default_outputs: assert property (
        @($global_clock) (op_select == 2'b11) |-> (result == 4'b0000) && (carry_borrow == 1'b0)
    );

    // Outputs remain unchanged if inputs a, b, and op_select are unchanged.
    check_outputs_stable_when_inputs_stable: assert property (
        @($global_clock) ($stable(a) && $stable(b) && $stable(op_select)) |-> $stable({carry_borrow, result})
    );

    // For subtraction, equal operands yield zero result and no borrow.
    check_sub_equal_operands_zero_result: assert property (
        @($global_clock) (op_select == 2'b01 && a == b) |-> (result == 4'b0000) && (carry_borrow == 1'b0)
    );

    // For AND, if either operand is zero, result is zero.
    check_and_zero_operand_zero_result: assert property (
        @($global_clock) (op_select == 2'b10 && ((a == 4'b0000) || (b == 4'b0000))) |-> (result == 4'b0000)
    );

    // For AND, result has no bits set outside those set in a and b.
    check_and_result_subset_inputs: assert property (
        @($global_clock) (op_select == 2'b10) |-> (((result & ~a) == 4'b0000) && ((result & ~b) == 4'b0000))
    );
endmodule