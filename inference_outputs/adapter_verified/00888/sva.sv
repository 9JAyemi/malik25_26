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

// out_and is the 4-bit AND of all four inputs.
    check_and_result: assert property (
        @(posedge clk) out_and == (in1 & in2 & in3 & in4)
    );

// out_or is the 4-bit OR of all four inputs.
    check_or_result: assert property (
        @(posedge clk) out_or == (in1 | in2 | in3 | in4)
    );

// out_xor is the 4-bit XOR of all four inputs.
    check_xor_result: assert property (
        @(posedge clk) out_xor == (in1 ^ in2 ^ in3 ^ in4)
    );

// If all inputs are zero, all outputs must be zero.
    check_zero_inputs_zero_outputs: assert property (
        @(posedge clk) ((in1 == 4'b0000) && (in2 == 4'b0000) && (in3 == 4'b0000) && (in4 == 4'b0000)) |-> ((out_and == 4'b0000) && (out_or == 4'b0000) && (out_xor == 4'b0000))
    );

// If any input is all ones, out_or must be all ones.
    check_any_all_ones_out_or_all_ones: assert property (
        @(posedge clk) ((in1 == 4'b1111) || (in2 == 4'b1111) || (in3 == 4'b1111) || (in4 == 4'b1111)) |-> (out_or == 4'b1111)
    );

// If any input is all ones, out_and must be all ones.
    check_any_all_ones_out_and_all_ones: assert property (
        @(posedge clk) ((in1 == 4'b1111) || (in2 == 4'b1111) || (in3 == 4'b1111) || (in4 == 4'b1111)) |-> (out_and == 4'b1111)
    );

// If all inputs are equal, out_xor must be zero.
    check_equal_inputs_zero_xor: assert property (
        @(posedge clk) ((in1 == in2) && (in2 == in3) && (in3 == in4)) |-> (out_xor == 4'b0000)
    );

endmodule
