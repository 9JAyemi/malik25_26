module add_sub_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       sub,
    input logic [3:0] result
);

    // The output must follow the RTL's add/sub select equation.
    check_selected_operation_equation: assert property (
        @($global_clock) result == (sub ? (A + ((~B) + 4'd1)) : (A + B))
    );

    // In add mode, result must be the 4-bit sum of A and B.
    check_add_mode_result: assert property (
        @($global_clock) !sub |-> (result == (A + B))
    );

    // In subtract mode, result must be the 4-bit difference A - B.
    check_sub_mode_result: assert property (
        @($global_clock) sub |-> (result == (A - B))
    );

    // Adding zero on B must leave A unchanged.
    check_add_zero_b_passthrough_a: assert property (
        @($global_clock) (!sub && (B == 4'd0)) |-> (result == A)
    );

    // Adding with A at zero must pass B through.
    check_add_zero_a_passthrough_b: assert property (
        @($global_clock) (!sub && (A == 4'd0)) |-> (result == B)
    );

    // Subtracting zero on B must leave A unchanged.
    check_sub_zero_b_passthrough_a: assert property (
        @($global_clock) (sub && (B == 4'd0)) |-> (result == A)
    );

    // Subtracting equal operands must produce zero.
    check_sub_equal_operands_zero: assert property (
        @($global_clock) (sub && (A == B)) |-> (result == 4'd0)
    );

    // With A at zero, subtraction must produce the 2's complement of B.
    check_sub_zero_a_twos_complement_b: assert property (
        @($global_clock) (sub && (A == 4'd0)) |-> (result == ((~B) + 4'd1))
    );

    // 4-bit addition must wrap on overflow.
    check_add_overflow_wraparound: assert property (
        @($global_clock) (!sub && (A == 4'hF) && (B == 4'd1)) |-> (result == 4'd0)
    );

    // 4-bit subtraction must wrap on underflow.
    check_sub_underflow_wraparound: assert property (
        @($global_clock) (sub && (A == 4'd0) && (B == 4'd1)) |-> (result == 4'hF)
    );

endmodule