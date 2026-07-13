module SimpleCalculator_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic op,
    input logic [3:0] result
);

// Result matches the selected arithmetic operation.
    check_function_select: assert property (
        @(posedge clk) result == (op ? (a - b) : (a + b))
    );

// When op is 0, result is the 4-bit sum of a and b.
    check_addition_result: assert property (
        @(posedge clk) (op == 1'b0) |-> (result == (a + b))
    );

// When op is 1, result is the 4-bit difference of a and b.
    check_subtraction_result: assert property (
        @(posedge clk) (op == 1'b1) |-> (result == (a - b))
    );

// Zero on b passes a through unchanged regardless of op.
    check_b_zero_passthrough: assert property (
        @(posedge clk) (b == 4'h0) |-> (result == a)
    );

// Zero on a returns b when adding, or 0 when subtracting.
    check_a_zero_behavior: assert property (
        @(posedge clk) (a == 4'h0) |-> ((op == 1'b0) ? (result == b) : (result == 4'h0))
    );

// Equal operands yield zero on subtraction.
    check_equal_operands_subtract_zero: assert property (
        @(posedge clk) (op == 1'b1) && (a == b) |-> (result == 4'h0)
    );

// Adding 1 to zero on a returns 1.
    check_add_one_to_zero: assert property (
        @(posedge clk) (op == 1'b0) && (a == 4'h0) && (b == 4'h1) |-> (result == 4'h1)
    );

// Subtracting 1 from zero on a returns 15.
    check_sub_one_from_zero: assert property (
        @(posedge clk) (op == 1'b1) && (a == 4'h0) && (b == 4'h1) |-> (result == 4'hF)
    );

endmodule
