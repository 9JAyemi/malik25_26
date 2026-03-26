module calculator_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic op,
    input logic [3:0] result
);

    // Addition mode drives result to A plus B.
    check_addition_mode: assert property (
        @(posedge clk) (op == 1'b1) |-> (result == (A + B))
    );

    // Subtraction mode drives result to A minus B.
    check_subtraction_mode: assert property (
        @(posedge clk) (op == 1'b0) |-> (result == (A - B))
    );

    // Result always matches the operation selected by op.
    check_selected_operation: assert property (
        @(posedge clk) result == (op ? (A + B) : (A - B))
    );

    // Adding zero on B leaves A unchanged.
    check_add_zero_identity: assert property (
        @(posedge clk) (op == 1'b1 && B == 4'h0) |-> (result == A)
    );

    // Subtracting zero leaves A unchanged.
    check_subtract_zero_identity: assert property (
        @(posedge clk) (op == 1'b0 && B == 4'h0) |-> (result == A)
    );

    // Subtracting equal operands produces zero.
    check_equal_operands_subtract_zero: assert property (
        @(posedge clk) (op == 1'b0 && A == B) |-> (result == 4'h0)
    );

endmodule