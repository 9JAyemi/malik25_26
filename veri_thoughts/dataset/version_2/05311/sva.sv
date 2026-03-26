module top_module_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] G
);

    // External sampling clock; RTL has no reset and is purely combinational.

    // G must always implement the greater-of-two function.
    check_g_matches_max_function: assert property (
        @(posedge clk) G == ((A > B) ? A : B)
    );

    // When A is greater than B, G must equal A.
    check_a_greater_selects_a: assert property (
        @(posedge clk) (A > B) |-> (G == A)
    );

    // When A is not greater than B, G must equal B.
    check_a_not_greater_selects_b: assert property (
        @(posedge clk) (A <= B) |-> (G == B)
    );

    // When A and B are equal, G must equal that shared value.
    check_equal_inputs_select_shared_value: assert property (
        @(posedge clk) (A == B) |-> (G == A)
    );

    // G must always be one of the two inputs.
    check_g_is_one_of_the_inputs: assert property (
        @(posedge clk) ((G == A) || (G == B))
    );

    // G must never be less than A.
    check_g_not_less_than_a: assert property (
        @(posedge clk) (G >= A)
    );

    // G must never be less than B.
    check_g_not_less_than_b: assert property (
        @(posedge clk) (G >= B)
    );

endmodule