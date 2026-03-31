module four_to_one_sva (
    input logic clk,
    input logic input1,
    input logic input2,
    input logic input3,
    input logic input4,
    input logic output1
);

// Output must match the OR of the four inputs.
    check_output_matches_or: assert property (
        @(posedge clk) output1 == (input1 | input2 | input3 | input4)
    );

// A high input1 must drive the output high.
    check_input1_sets_output: assert property (
        @(posedge clk) input1 |-> output1
    );

// A high input2 must drive the output high.
    check_input2_sets_output: assert property (
        @(posedge clk) input2 |-> output1
    );

// A high input3 must drive the output high.
    check_input3_sets_output: assert property (
        @(posedge clk) input3 |-> output1
    );

// A high input4 must drive the output high.
    check_input4_sets_output: assert property (
        @(posedge clk) input4 |-> output1
    );

// A low output implies all four inputs are low.
    check_output_low_implies_all_inputs_low: assert property (
        @(posedge clk) !output1 |-> (!input1 && !input2 && !input3 && !input4)
    );

// A high output implies at least one input is high.
    check_output_high_implies_some_input_high: assert property (
        @(posedge clk) output1 |-> (input1 || input2 || input3 || input4)
    );

endmodule
