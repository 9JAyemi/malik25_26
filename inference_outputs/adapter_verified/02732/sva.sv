module top_module_sva (
    input logic CLK,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [3:0] shift_amount,
    input logic [15:0] result
);

// Result matches the RTL's full conditional expression.
    check_full_result_function: assert property (
        @(posedge CLK) result == ((A > B) ? (A << shift_amount) : ((A < B) ? (B >> shift_amount) : A))
    );

// When A is greater than B, result is A shifted left by shift_amount.
    check_left_shift_when_A_greater: assert property (
        @(posedge CLK) (A > B) |-> (result == (A << shift_amount))
    );

// When A is less than B, result is B shifted right by shift_amount.
    check_right_shift_when_A_less: assert property (
        @(posedge CLK) (A < B) |-> (result == (B >> shift_amount))
    );

// When A equals B, result passes through A.
    check_passthrough_when_equal: assert property (
        @(posedge CLK) (A == B) |-> (result == A)
    );

// Zero shift amount always passes through A.
    check_zero_shift_passthrough: assert property (
        @(posedge CLK) (shift_amount == 4'h0) |-> (result == (A_greater_B ? A : B))
    );

// Maximum shift amount drives zero on the selected path.
    check_max_shift_zero: assert property (
        @(posedge CLK) (shift_amount == 4'hF) |-> (result == (A_greater_B ? 16'h0000 : B))
    );

// Left shift by 1 maps A to A[14:0] with zero in bit 15.
    check_left_shift_by_one: assert property (
        @(posedge CLK) (A_greater_B && (shift_amount == 4'h1)) |-> (result == {1'b0, A[14:0]})
    );

// Right shift by 1 maps B to B[1:0] with zero in bit 15.
    check_right_shift_by_one: assert property (
        @(posedge CLK) (A < B && (shift_amount == 4'h1)) |-> (result == {14'b0, B[1:0]})
    );

endmodule
