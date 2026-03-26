module calculator_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       op,
    input logic [3:0] result
);

    // Result always matches the selected arithmetic operation.
    check_result_matches_operation: assert property (
        @($global_clock) result == (op ? (a - b) : (a + b))
    );

    // In add mode, result is the 4-bit sum of a and b.
    check_add_mode_result: assert property (
        @($global_clock) (!op) |-> (result == (a + b))
    );

    // In subtract mode, result is the 4-bit difference of a and b.
    check_subtract_mode_result: assert property (
        @($global_clock) op |-> (result == (a - b))
    );

    // Adding zero on b leaves a unchanged.
    check_add_zero_on_b_identity: assert property (
        @($global_clock) (!op && (b == 4'b0000)) |-> (result == a)
    );

    // Subtracting zero leaves a unchanged.
    check_subtract_zero_identity: assert property (
        @($global_clock) (op && (b == 4'b0000)) |-> (result == a)
    );

    // Subtracting equal operands yields zero.
    check_subtract_equal_operands_zero: assert property (
        @($global_clock) (op && (a == b)) |-> (result == 4'b0000)
    );

endmodule