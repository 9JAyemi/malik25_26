module five_to_one_sva (
    input logic clk,
    input logic input1,
    input logic input2,
    input logic input3,
    input logic input4,
    input logic input5,
    input logic output1
);

    // Output matches the RTL sum-of-products equation.
    check_output_equation: assert property (
        @(posedge clk)
        output1 == ((input1 & input2) | (input3 & input4 & input5))
    );

    // The input1/input2 AND path forces the output high.
    check_first_path_drives_high: assert property (
        @(posedge clk)
        (input1 & input2) |-> output1
    );

    // The input3/input4/input5 AND path forces the output high.
    check_second_path_drives_high: assert property (
        @(posedge clk)
        (input3 & input4 & input5) |-> output1
    );

    // A high output must come from at least one implemented path.
    check_output_high_has_valid_cause: assert property (
        @(posedge clk)
        output1 |-> ((input1 & input2) | (input3 & input4 & input5))
    );

    // If the first path is inactive, output equals the second path.
    check_no_first_path_means_second_path_only: assert property (
        @(posedge clk)
        !(input1 & input2) |-> (output1 == (input3 & input4 & input5))
    );

    // If the second path is inactive, output equals the first path.
    check_no_second_path_means_first_path_only: assert property (
        @(posedge clk)
        !(input3 & input4 & input5) |-> (output1 == (input1 & input2))
    );

endmodule