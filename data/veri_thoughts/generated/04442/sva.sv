module digital_circuit_sva (
    input logic clk,
    input logic input_1,
    input logic input_2,
    input logic input_3,
    input logic input_4,
    input logic output_1,
    input logic output_2
);

    // output_1 must equal the AND of input_1 and input_2.
    check_output_1_and: assert property (
        @(posedge clk) output_1 == (input_1 & input_2)
    );

    // output_2 must equal the OR of input_3 and input_4.
    check_output_2_or: assert property (
        @(posedge clk) output_2 == (input_3 | input_4)
    );

endmodule