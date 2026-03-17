module two_input_and_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic y
);

    // Output must equal the AND of the two inputs.
    check_y_matches_and: assert property (
        @(posedge clk) y == (a & b)
    );

    // A high output requires both inputs high.
    check_y_high_requires_both_inputs_high: assert property (
        @(posedge clk) y |-> (a && b)
    );

    // Both inputs high must produce a high output.
    check_both_inputs_high_produces_y_high: assert property (
        @(posedge clk) (a && b) |-> y
    );

    // A low on input a forces the output low.
    check_a_low_forces_y_low: assert property (
        @(posedge clk) !a |-> !y
    );

    // A low on input b forces the output low.
    check_b_low_forces_y_low: assert property (
        @(posedge clk) !b |-> !y
    );

endmodule