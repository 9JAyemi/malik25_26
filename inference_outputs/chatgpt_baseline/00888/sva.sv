module pipelined_bitwise_operations_sva (
    input logic clk,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [3:0] in4,
    input logic [3:0] out_and,
    input logic [3:0] out_or,
    input logic [3:0] out_xor
);

    ///// Functional equivalence checks /////
    // out_and equals bitwise AND of all inputs.
    spec_out_and_def: assert property (
        @(posedge clk) out_and == (((in1 & in2) & in3) & in4)
    );

    // out_or equals bitwise OR of all inputs.
    spec_out_or_def: assert property (
        @(posedge clk) out_or == (((in1 | in2) | in3) | in4)
    );

    // out_xor equals bitwise XOR of all inputs.
    spec_out_xor_def: assert property (
        @(posedge clk) out_xor == (((in1 ^ in2) ^ in3) ^ in4)
    );

    ///// AND result subset relations /////
    // out_and cannot have 1s where in1 has 0s.
    check_and_subset_in1: assert property (
        @(posedge clk) (out_and & ~in1) == 4'b0000
    );

    // out_and cannot have 1s where in2 has 0s.
    check_and_subset_in2: assert property (
        @(posedge clk) (out_and & ~in2) == 4'b0000
    );

    // out_and cannot have 1s where in3 has 0s.
    check_and_subset_in3: assert property (
        @(posedge clk) (out_and & ~in3) == 4'b0000
    );

    // out_and cannot have 1s where in4 has 0s.
    check_and_subset_in4: assert property (
        @(posedge clk) (out_and & ~in4) == 4'b0000
    );

    ///// OR result superset relations /////
    // out_or must have 1s wherever in1 has 1s.
    check_or_superset_in1: assert property (
        @(posedge clk) (in1 & ~out_or) == 4'b0000
    );

    // out_or must have 1s wherever in2 has 1s.
    check_or_superset_in2: assert property (
        @(posedge clk) (in2 & ~out_or) == 4'b0000
    );

    // out_or must have 1s wherever in3 has 1s.
    check_or_superset_in3: assert property (
        @(posedge clk) (in3 & ~out_or) == 4'b0000
    );

    // out_or must have 1s wherever in4 has 1s.
    check_or_superset_in4: assert property (
        @(posedge clk) (in4 & ~out_or) == 4'b0000
    );

    ///// Cross-output relation /////
    // AND result is always a subset of OR result.
    check_and_implies_or: assert property (
        @(posedge clk) (out_and & ~out_or) == 4'b0000
    );

endmodule