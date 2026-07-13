module greater_than_module_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] x
);

    // x equals the max of a and b per RTL conditional
    check_output_is_max_expr: assert property (
        @(posedge clk) x == ((a > b) ? a : b)
    );

    // When a > b, x must be a
    check_select_a_when_a_gt_b: assert property (
        @(posedge clk) (a > b) |-> (x == a)
    );

    // When a <= b, x must be b
    check_select_b_when_a_le_b: assert property (
        @(posedge clk) (a <= b) |-> (x == b)
    );

    // On tie (a == b), x selects b
    check_select_b_on_tie: assert property (
        @(posedge clk) (a == b) |-> (x == b)
    );

    // x must always equal either a or b
    check_x_equals_a_or_b_only: assert property (
        @(posedge clk) (x == a) || (x == b)
    );

    // If x equals a, then a must be greater than b
    check_if_x_is_a_then_a_gt_b: assert property (
        @(posedge clk) (x == a) |-> (a > b)
    );

    // If x equals b, then a must be less than or equal to b
    check_if_x_is_b_then_a_le_b: assert property (
        @(posedge clk) (x == b) |-> (a <= b)
    );

    // x is at least as large as a
    check_x_ge_a: assert property (
        @(posedge clk) (x >= a)
    );

    // x is at least as large as b
    check_x_ge_b: assert property (
        @(posedge clk) (x >= b)
    );

    // If either input is 4'hF, x must be 4'hF
    check_x_is_F_if_any_F: assert property (
        @(posedge clk) ((a == 4'hF) || (b == 4'hF)) |-> (x == 4'hF)
    );

    // If both inputs are zero, x must be zero
    check_x_is_zero_if_both_zero: assert property (
        @(posedge clk) ((a == 4'h0) && (b == 4'h0)) |-> (x == 4'h0)
    );

endmodule