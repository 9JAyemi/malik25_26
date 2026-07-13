module SimpleCalculator_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       op,
    input logic [3:0] result
);

    // Result must match the selected arithmetic operation.
    check_result_matches_operation: assert property (
        @($global_clock) result == (op ? (a - b) : (a + b))
    );

    // In addition mode, result must equal a plus b.
    check_add_mode_result: assert property (
        @($global_clock) (op == 1'b0) |-> (result == (a + b))
    );

    // In subtraction mode, result must equal a minus b.
    check_sub_mode_result: assert property (
        @($global_clock) (op == 1'b1) |-> (result == (a - b))
    );

    // With b equal to zero, result must pass a through.
    check_zero_b_passthrough: assert property (
        @($global_clock) (b == 4'h0) |-> (result == a)
    );

    // In addition mode with a equal to zero, result must pass b through.
    check_add_zero_a_passthrough: assert property (
        @($global_clock) ((op == 1'b0) && (a == 4'h0)) |-> (result == b)
    );

    // In subtraction mode with a equal to zero, result must be the two's complement of b.
    check_sub_zero_a_twos_complement: assert property (
        @($global_clock) ((op == 1'b1) && (a == 4'h0)) |-> (result == ~b + 4'h1)
    );

endmodule