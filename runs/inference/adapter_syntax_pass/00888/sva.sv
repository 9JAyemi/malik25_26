module pipelined_bitwise_operations_sva (
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [3:0] in4,
    input logic [3:0] out_and,
    input logic [3:0] out_or,
    input logic [3:0] out_xor
);

    // out_and matches the 4-bit AND of all four inputs.
    check_out_and_matches_inputs: assert property (
        @($global_clock) out_and == (in1 & in2 & in3 & in4)
    );

    // out_or matches the 4-bit OR of all four inputs.
    check_out_or_matches_inputs: assert property (
        @($global_clock) out_or == (in1 | in2 | in3 | in4)
    );

    // out_xor matches the 4-bit XOR of all four inputs.
    check_out_xor_matches_inputs: assert property (
        @($global_clock) out_xor == (in1 ^ in2 ^ in3 ^ in4)
    );

    // out_and is a subset of out_or.
    check_out_and_subset_of_out_or: assert property (
        @($global_clock) (out_and & ~out_or) == 4'h0
    );

    // out_and and out_xor are mutually exclusive.
    check_out_and_xor_disjoint: assert property (
        @($global_clock) (out_and & out_xor) == 4'h0
    );

    // out_or equals the OR of out_and and out_xor.
    check_out_or_equals_out_and_or_out_xor: assert property (
        @($global_clock) out_or == (out_and | out_xor)
    );

    // out_xor equals the XOR of out_and and out_or.
    check_out_xor_equals_out_and_xor_out_or: assert property (
        @($global_clock) out_xor == (out_and ^ out_or)
    );

    // All-zero inputs produce all-zero outputs.
    check_zero_inputs_zero_outputs: assert property (
        @($global_clock) ((in1 == 4'h0) && (in2 == 4'h0) && (in3 == 4'h0) && (in4 == 4'h0))
        |-> ((out_and == 4'h0) && (out_or == 4'h0) && (out_xor == 4'h0))
    );

    // All-one inputs produce all-one outputs.
    check_all_one_inputs_all_one_outputs: assert property (
        @($global_clock) ((in1 == 4'hF) && (in2 == 4'hF) && (in3 == 4'hF) && (in4 == 4'hF))
        |-> ((out_and == 4'hF) && (out_or == 4'hF) && (out_xor == 4'h0))
    );

    // Equal inputs make out_xor zero and out_or equal to the inputs.
    check_equal_inputs_behavior: assert property (
        @($global_clock) (in1 == in2 && in2 == in3 && in3 == in4)
        |-> ((out_and == in1) && (out_or == in1) && (out_xor == 4'h0))
    );

endmodule