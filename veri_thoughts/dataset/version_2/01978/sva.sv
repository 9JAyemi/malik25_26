module top_module_sva (
    input logic CLK,
    input logic [99:0] in1,
    input logic [99:0] in2,
    input logic [99:0] out_and
);
    // out_and equals bitwise AND of inputs.
    check_and_function: assert property (
        @(posedge CLK) disable iff (1'b0) out_and == (in1 & in2)
    );

    // out_and matches the composed structure (in1|in2)^(in1^in2).
    check_structural_equivalence: assert property (
        @(posedge CLK) disable iff (1'b0) out_and == ((in1 | in2) ^ (in1 ^ in2))
    );

    // All 1s in out_and must be a subset of in1.
    check_subset_in1: assert property (
        @(posedge CLK) disable iff (1'b0) (out_and & ~in1) == '0
    );

    // All 1s in out_and must be a subset of in2.
    check_subset_in2: assert property (
        @(posedge CLK) disable iff (1'b0) (out_and & ~in2) == '0
    );

    // If in1 is all zeros, out_and is all zeros.
    check_zero_mask_in1: assert property (
        @(posedge CLK) disable iff (1'b0) (in1 == '0) |-> (out_and == '0)
    );

    // If in2 is all zeros, out_and is all zeros.
    check_zero_mask_in2: assert property (
        @(posedge CLK) disable iff (1'b0) (in2 == '0) |-> (out_and == '0)
    );

    // If in1 is all ones, out_and equals in2.
    check_allones_mask_in1: assert property (
        @(posedge CLK) disable iff (1'b0) (in1 == '1) |-> (out_and == in2)
    );

    // If in2 is all ones, out_and equals in1.
    check_allones_mask_in2: assert property (
        @(posedge CLK) disable iff (1'b0) (in2 == '1) |-> (out_and == in1)
    );

    // If inputs are equal, out_and equals that value.
    check_equal_inputs: assert property (
        @(posedge CLK) disable iff (1'b0) (in1 == in2) |-> (out_and == in1)
    );

    // If inputs are bitwise complements, out_and is all zeros.
    check_complementary_inputs: assert property (
        @(posedge CLK) disable iff (1'b0) (in2 == ~in1) |-> (out_and == '0)
    );
endmodule