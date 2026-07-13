module adder_subtractor_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUB,
    input logic [3:0] SUM
);

    // SUM must match the selected add or subtract operation.
    check_sum_function: assert property (
        @($global_clock) SUM == (SUB ? (A + (~B + 4'b0001)) : (A + B))
    );

    // In add mode, SUM must equal A plus B.
    check_add_mode: assert property (
        @($global_clock) !SUB |-> (SUM == (A + B))
    );

    // In subtract mode, SUM must equal A plus the two's complement of B.
    check_subtract_mode: assert property (
        @($global_clock) SUB |-> (SUM == (A + (~B + 4'b0001)))
    );

    // With B equal to zero, SUM must pass A through.
    check_zero_b_passthrough: assert property (
        @($global_clock) (B == 4'b0000) |-> (SUM == A)
    );

    // With A equal to zero, SUM must equal B in add mode and the two's complement of B in subtract mode.
    check_zero_a_behavior: assert property (
        @($global_clock) (A == 4'b0000) |-> (SUM == (SUB ? (~B + 4'b0001) : B))
    );

    // In add mode, adding zero on B must leave A unchanged.
    check_add_zero_b_identity: assert property (
        @($global_clock) (!SUB && (B == 4'b0000)) |-> (SUM == A)
    );

    // In subtract mode, subtracting zero on B must leave A unchanged.
    check_subtract_zero_b_identity: assert property (
        @($global_clock) (SUB && (B == 4'b0000)) |-> (SUM == A)
    );

    // In add mode, adding zero on A must leave B unchanged.
    check_add_zero_a_identity: assert property (
        @($global_clock) (!SUB && (A == 4'b0000)) |-> (SUM == B)
    );

    // In subtract mode, subtracting zero on A must leave B unchanged.
    check_subtract_zero_a_identity: assert property (
        @($global_clock) (SUB && (A == 4'b0000)) |-> (SUM == (~B + 4'b0001))
    );

    // In add mode, adding 4'hF on B must produce 4'h1 on the next cycle.
    check_add_max_b_behavior: assert property (
        @($global_clock) (!SUB && (B == 4'hF)) |-> ##1 (SUM == 4'h1)
    );

    // In subtract mode, subtracting 4'hF on B must produce 4'hF on the next cycle.
    check_subtract_max_b_behavior: assert property (
        @($global_clock) (SUB && (B == 4'hF)) |-> ##1 (SUM == 4'hF)
    );

endmodule