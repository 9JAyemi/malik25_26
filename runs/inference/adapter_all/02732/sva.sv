module top_module_sva (
    input logic        clk,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [3:0]  shift_amount,
    input logic [15:0] result
);

    // No RTL clock or reset; clk is an external sampling clock.

    // When A is greater than B, result is A shifted left by shift_amount.
    check_a_greater_b_shifts_a: assert property (
        @(posedge clk) (A > B) |-> (result == (A << shift_amount))
    );

    // When A is less than B, result is B shifted right by shift_amount.
    check_a_less_b_shifts_b: assert property (
        @(posedge clk) (A < B) |-> (result == (B >> shift_amount))
    );

    // When A equals B, result passes through A.
    check_equal_inputs_pass_a: assert property (
        @(posedge clk) (A == B) |-> (result == A)
    );

    // A zero shift amount leaves the selected input unchanged.
    check_zero_shift_passthrough: assert property (
        @(posedge clk) (shift_amount == 4'd0) |-> (result == (A > B ? A : B))
    );

    // A zero shift amount with equal inputs passes through A.
    check_zero_shift_equal_inputs_pass_a: assert property (
        @(posedge clk) ((shift_amount == 4'd0) && (A == B)) |-> (result == A)
    );

    // A zero shift amount with A greater than B passes through A.
    check_zero_shift_a_greater_b_pass_a: assert property (
        @(posedge clk) ((shift_amount == 4'd0) && (A > B)) |-> (result == A)
    );

    // A zero shift amount with A less than B passes through B.
    check_zero_shift_a_less_b_pass_b: assert property (
        @(posedge clk) ((shift_amount == 4'd0) && (A < B)) |-> (result == B)
    );

    // A zero shift amount with A greater than B and equal MSBs returns A.
    check_zero_shift_a_greater_b_equal_msb_pass_a: assert property (
        @(posedge clk) ((shift_amount == 4'd0) && (A > B) && (A[15] == B[15])) |-> (result == A)
    );

    // A zero shift amount with A less than B and equal MSBs returns B.
    check_zero_shift_a_less_b_equal_msb_pass_b: assert property (
        @(posedge clk) ((shift_amount == 4'd0) && (A < B) && (A[15] == B[15])) |-> (result == B)
    );

    // A zero shift amount with A less than B and different MSBs returns B.
    check_zero_shift_a_less_b_different_msb_pass_b: assert property (
        @(posedge clk) ((shift_amount == 4'd0) && (A < B) && (A[15] != B[15])) |-> (result == B)
    );

endmodule