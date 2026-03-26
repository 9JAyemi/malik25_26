module greater_of_two_assertions (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] G
);

    // If A is greater than B, G must equal A.
    check_select_a_when_a_gt_b: assert property (
        @(posedge clk) (A > B) |-> (G == A)
    );

    // If A is less than or equal to B, G must equal B.
    check_select_b_when_a_le_b: assert property (
        @(posedge clk) (A <= B) |-> (G == B)
    );

    // G must never be smaller than A.
    check_g_not_less_than_a: assert property (
        @(posedge clk) (G >= A)
    );

    // G must never be smaller than B.
    check_g_not_less_than_b: assert property (
        @(posedge clk) (G >= B)
    );

    // G must always match one of the two inputs.
    check_g_matches_one_input: assert property (
        @(posedge clk) ((G == A) || (G == B))
    );

    // If A and B are equal, G must equal that shared value.
    check_equal_inputs_return_that_value: assert property (
        @(posedge clk) (A == B) |-> (G == A)
    );

endmodule