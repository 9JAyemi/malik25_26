module max_byte_sva (
    input logic        clk,
    input logic [7:0]  a,
    input logic [7:0]  b,
    input logic [7:0]  max_val
);

    // max_val matches the RTL max function.
    check_max_function: assert property (
        @(posedge clk) max_val == ((a >= b) ? a : b)
    );

    // When a is at least b, max_val selects a.
    check_select_a_when_a_ge_b: assert property (
        @(posedge clk) (a >= b) |-> (max_val == a)
    );

    // When b is greater than a, max_val selects b.
    check_select_b_when_b_gt_a: assert property (
        @(posedge clk) (a < b) |-> (max_val == b)
    );

    // max_val is never smaller than a.
    check_max_not_less_than_a: assert property (
        @(posedge clk) max_val >= a
    );

    // max_val is never smaller than b.
    check_max_not_less_than_b: assert property (
        @(posedge clk) max_val >= b
    );

    // max_val must equal one of the inputs.
    check_max_matches_input: assert property (
        @(posedge clk) (max_val == a) || (max_val == b)
    );

    // Equal inputs pass through unchanged.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (a == b) |-> (max_val == a)
    );

endmodule