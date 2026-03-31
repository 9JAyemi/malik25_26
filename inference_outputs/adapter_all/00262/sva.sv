module four_to_one_sva (
    input logic clk,
    input logic input1,
    input logic input2,
    input logic input3,
    input logic input4,
    input logic output1
);

    // Output must match the OR of all four inputs.
    check_output_matches_or: assert property (
        @(posedge clk) output1 == (input1 | input2 | input3 | input4)
    );

    // If any input is high, the output must be high.
    check_any_input_high_sets_output: assert property (
        @(posedge clk) (input1 | input2 | input3 | input4) |-> output1
    );

    // If all inputs are low, the output must be low.
    check_all_inputs_low_clears_output: assert property (
        @(posedge clk) !(input1 | input2 | input3 | input4) |-> !output1
    );

    // A high output must come from at least one high input.
    check_output_high_has_active_input: assert property (
        @(posedge clk) output1 |-> (input1 | input2 | input3 | input4)
    );

    // A low output means all inputs are low.
    check_output_low_means_all_inputs_low: assert property (
        @(posedge clk) !output1 |-> !(input1 | input2 | input3 | input4)
    );

endmodule