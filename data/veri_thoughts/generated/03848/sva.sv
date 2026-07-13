module or4_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);

    // X must equal the OR of all four inputs.
    check_output_matches_or_function: assert property (
        @(posedge clk) X == (A | B | C | D)
    );

    // If any input is HIGH, X must be HIGH.
    check_output_high_when_any_input_high: assert property (
        @(posedge clk) (A | B | C | D) |-> X
    );

    // If all inputs are LOW, X must be LOW.
    check_output_low_when_all_inputs_low: assert property (
        @(posedge clk) !(A | B | C | D) |-> !X
    );

    // If X is HIGH, at least one input must be HIGH.
    check_output_high_implies_some_input_high: assert property (
        @(posedge clk) X |-> (A | B | C | D)
    );

endmodule