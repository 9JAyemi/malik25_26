module adder_subtractor_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUB,
    input logic [3:0] result,
    input logic OVFL
);

    // In add mode, result is A plus B.
    check_add_mode_result: assert property (
        @($global_clock) (SUB == 1'b0) |-> (result == (A + B))
    );

    // In subtract mode, result is A minus B.
    check_sub_mode_result: assert property (
        @($global_clock) (SUB == 1'b1) |-> (result == (A - B))
    );

    // In add mode, OVFL is high only when the top bit of result is set.
    check_add_mode_overflow: assert property (
        @($global_clock) (SUB == 1'b0) |-> (OVFL == result[3])
    );

    // In subtract mode, OVFL is high only when the top bit of result is set.
    check_sub_mode_overflow: assert property (
        @($global_clock) (SUB == 1'b1) |-> (OVFL == result[3])
    );

    // OVFL always matches the top bit of the computed result.
    check_overflow_matches_result_bit: assert property (
        @($global_clock) OVFL == result[3]
    );

endmodule