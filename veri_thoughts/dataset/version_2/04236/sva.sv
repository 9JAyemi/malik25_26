module top_module_sva (
    input logic        clk,
    input logic        reset,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic        sub,
    input logic        enable,
    input logic [31:0] sum
);

    // sum matches the selected add/subtract operation.
    check_sum_selected_operation: assert property (
        @(posedge clk) disable iff (reset)
        sum == (a + (sub ? (~b + 32'd1) : b))
    );

    // sum is a+b when subtraction is not selected.
    check_addition_mode: assert property (
        @(posedge clk) disable iff (reset)
        !sub |-> (sum == (a + b))
    );

    // sum is a-b in two's-complement form when subtraction is selected.
    check_subtraction_mode: assert property (
        @(posedge clk) disable iff (reset)
        sub |-> (sum == (a + (~b + 32'd1)))
    );

    // Holding a, b, and sub stable keeps sum stable.
    check_sum_stable_when_operands_stable: assert property (
        @(posedge clk) disable iff (reset)
        (!$past(reset) && $stable({a, b, sub})) |-> $stable(sum)
    );

    // Changing enable alone does not affect the combinational sum output.
    check_enable_independent_of_sum: assert property (
        @(posedge clk) disable iff (reset)
        (!$past(reset) && $changed(enable) && $stable({a, b, sub})) |-> $stable(sum)
    );

    // Subtracting equal operands produces zero.
    check_sub_equal_operands_zero: assert property (
        @(posedge clk) disable iff (reset)
        sub && (a == b) |-> (sum == 32'd0)
    );

endmodule