module four_to_one_sva (
    input logic clk,
    input logic input1,
    input logic input2,
    input logic input3,
    input logic input4,
    input logic output1
);

    // No clock or reset exists in the DUT; clk is an external sampling clock.
    // The DUT is purely combinational and implements a 4-input OR.

    // Output must equal the OR of all four inputs.
    check_output_matches_or: assert property (
        @(posedge clk)
        output1 === (input1 | input2 | input3 | input4)
    );

    // Any asserted input must drive the output high.
    check_any_high_sets_output: assert property (
        @(posedge clk)
        ((input1 | input2 | input3 | input4) === 1'b1) |-> (output1 === 1'b1)
    );

    // All deasserted inputs must drive the output low.
    check_all_low_clears_output: assert property (
        @(posedge clk)
        (input1 === 1'b0 && input2 === 1'b0 && input3 === 1'b0 && input4 === 1'b0) |-> (output1 === 1'b0)
    );

    // A high output requires at least one high input.
    check_output_high_implies_input_high: assert property (
        @(posedge clk)
        (output1 === 1'b1) |-> ((input1 | input2 | input3 | input4) === 1'b1)
    );

    // A low output requires all inputs to be low.
    check_output_low_implies_all_inputs_low: assert property (
        @(posedge clk)
        (output1 === 1'b0) |-> (input1 === 1'b0 && input2 === 1'b0 && input3 === 1'b0 && input4 === 1'b0)
    );

endmodule