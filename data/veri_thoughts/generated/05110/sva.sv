module Behavioral_PE_sva (
    input logic clk,
    input logic in2,
    input logic in1,
    input logic in0,
    input logic out1,
    input logic out0
);

    // All-zero input drives 10.
    check_all_zero_outputs: assert property (
        @(posedge clk)
        ({in2, in1, in0} == 3'b000) |-> (out1 == 1'b1 && out0 == 1'b0)
    );

    // All-one input drives 10.
    check_all_one_outputs: assert property (
        @(posedge clk)
        ({in2, in1, in0} == 3'b111) |-> (out1 == 1'b1 && out0 == 1'b0)
    );

    // Any mixed input pattern drives 01.
    check_mixed_inputs_outputs: assert property (
        @(posedge clk)
        (({in2, in1, in0} != 3'b000) && ({in2, in1, in0} != 3'b111)) |-> (out1 == 1'b0 && out0 == 1'b1)
    );

    // out1 can only be high for 000 or 111.
    check_out1_only_for_uniform_inputs: assert property (
        @(posedge clk)
        (out1 == 1'b1) |-> (({in2, in1, in0} == 3'b000) || ({in2, in1, in0} == 3'b111))
    );

    // out0 can only be high for non-uniform inputs.
    check_out0_only_for_mixed_inputs: assert property (
        @(posedge clk)
        (out0 == 1'b1) |-> (({in2, in1, in0} != 3'b000) && ({in2, in1, in0} != 3'b111))
    );

    // Outputs are always complementary.
    check_outputs_complementary: assert property (
        @(posedge clk)
        (out1 ^ out0)
    );

endmodule