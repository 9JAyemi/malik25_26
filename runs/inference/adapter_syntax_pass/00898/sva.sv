module adder_subtractor_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUB,
    input logic [3:0] SUM
);

    // SUM must match the selected add or subtract operation.
    check_sum_function: assert property (
        @($global_clock) SUM == ((SUB) ? (A + ((~B) + 4'd1)) : (A + B))
    );

    // In add mode, SUM must equal A plus B.
    check_add_mode: assert property (
        @($global_clock) !SUB |-> (SUM == (A + B))
    );

    // In subtract mode, SUM must equal A plus the two's complement of B.
    check_sub_mode: assert property (
        @($global_clock) SUB |-> (SUM == (A + ((~B) + 4'd1)))
    );

    // With B at zero, SUM must pass A through.
    check_zero_b_passthrough: assert property (
        @($global_clock) (B == 4'd0) |-> (SUM == A)
    );

    // In add mode with B at one, SUM must increment A by one.
    check_add_one_increment: assert property (
        @($global_clock) (!SUB && (B == 4'd1)) |-> (SUM == (A + 4'd1))
    );

    // In subtract mode with B at one, SUM must decrement A by one.
    check_sub_one_decrement: assert property (
        @($global_clock) (SUB && (B == 4'd1)) |-> (SUM == (A - 4'd1))
    );

    // In add mode with A at zero, SUM must equal B.
    check_add_zero_a_passthrough: assert property (
        @($global_clock) (!SUB && (A == 4'd0)) |-> (SUM == B)
    );

    // In subtract mode with A at zero, SUM must equal the two's complement of B.
    check_sub_zero_a_twos_complement: assert property (
        @($global_clock) (SUB && (A == 4'd0)) |-> (SUM == ((~B) + 4'd1))
    );

endmodule