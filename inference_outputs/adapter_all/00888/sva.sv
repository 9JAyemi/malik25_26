module pipelined_bitwise_operations_sva (
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [3:0] in4,
    input logic [3:0] out_and,
    input logic [3:0] out_or,
    input logic [3:0] out_xor
);

    // out_and matches the nested AND chain.
    check_out_and_chain: assert property (
        @($global_clock) out_and == (in1 & in2 & in3 & in4)
    );

    // out_or matches the nested OR chain.
    check_out_or_chain: assert property (
        @($global_clock) out_or == (in1 | in2 | in3 | in4)
    );

    // out_xor matches the nested XOR chain.
    check_out_xor_chain: assert property (
        @($global_clock) out_xor == (in1 ^ in2 ^ in3 ^ in4)
    );

    // All-zero inputs produce all-zero outputs.
    check_zero_inputs_zero_outputs: assert property (
        @($global_clock) ((in1 == 4'b0000) && (in2 == 4'b0000) && (in3 == 4'b0000) && (in4 == 4'b0000))
            |-> ((out_and == 4'b0000) && (out_or == 4'b0000) && (out_xor == 4'b0000))
    );

    // All-one inputs produce all-one outputs.
    check_all_ones_inputs_all_ones_outputs: assert property (
        @($global_clock) ((in1 == 4'b1111) && (in2 == 4'b1111) && (in3 == 4'b1111) && (in4 == 4'b1111))
            |-> ((out_and == 4'b1111) && (out_or == 4'b1111) && (out_xor == 4'b0000))
    );

    // Equal inputs produce equal outputs.
    check_equal_inputs_equal_outputs: assert property (
        @($global_clock) (in1 == in2) && (in2 == in3) && (in3 == in4)
            |-> (out_and == out_or) && (out_or == out_xor)
    );

    // Equal inputs produce zero XOR and all-ones OR.
    check_equal_inputs_xor_zero_or_all_ones: assert property (
        @($global_clock) (in1 == in2) && (in2 == in3) && (in3 == in4)
            |-> ((out_xor == 4'b0000) && (out_or == 4'b1111))
    );

    // Equal inputs produce zero AND only for zero inputs.
    check_equal_inputs_and_zero_only_for_zero: assert property (
        @($global_clock) (in1 == in2) && (in2 == in3) && (in3 == in4)
            |-> ((in1 == 4'b0000) |-> (out_and == 4'b0000))
    );

    // Equal inputs produce all-ones OR only for all-one inputs.
    check_equal_inputs_or_all_ones_only_for_all_ones: assert property (
        @($global_clock) (in1 == in2) && (in2 == in3) && (in3 == in4)
            |-> ((in1 == 4'b1111) |-> (out_or == 4'b1111))
    );

    // Equal inputs produce zero XOR only for zero inputs.
    check_equal_inputs_xor_zero_only_for_zero: assert property (
        @($global_clock) (in1 == in2) && (in2 == in3) && (in3 == in4)
            |-> ((in1 == 4'b0000) |-> (out_xor == 4'b0000))
    );

    // Equal inputs produce all-ones OR only for all-one inputs.
    check_equal_inputs_or_all_ones_only_for_all_ones: assert property (
        @($global_clock) (in1 == in2) && (in2 == in3) && (in3 == in4)
            |-> ((in1 == 4'b1111) |-> (out_or == 4'b1111))
    );

endmodule