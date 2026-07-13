module top_module_sva (
    input logic CLK,                 // External clock for SVA (RTL is combinational)
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [3:0] shift_amount,
    input logic [15:0] result
);
    // RTL has no reset; assertions are not reset-disabled.
    // Combinational behavior: if (A>B) result=A<<shift_amount; else if (A<B) result=B>>shift_amount; else result=A.

    // If A > B, result equals A shifted left by shift_amount.
    check_left_shift_when_A_gt_B: assert property (
        @(posedge CLK) (A > B) |-> (result == (A << shift_amount))
    );

    // If A < B, result equals B shifted right by shift_amount.
    check_right_shift_when_A_lt_B: assert property (
        @(posedge CLK) (A < B) |-> (result == (B >> shift_amount))
    );

    // If A == B, result equals A.
    check_passthrough_when_A_eq_B: assert property (
        @(posedge CLK) (A == B) |-> (result == A)
    );

    // If shift_amount is 0 and A > B, result equals A (no left shift effect).
    check_no_shift_behavior_left: assert property (
        @(posedge CLK) ((A > B) && (shift_amount == 4'd0)) |-> (result == A)
    );

    // If shift_amount is 0 and A < B, result equals B (no right shift effect).
    check_no_shift_behavior_right: assert property (
        @(posedge CLK) ((A < B) && (shift_amount == 4'd0)) |-> (result == B)
    );

    // For left shift by >=1 (A > B), LSB of result is 0.
    check_lsb_zero_after_left_shift: assert property (
        @(posedge CLK) ((A > B) && (shift_amount != 4'd0)) |-> (result[0] == 1'b0)
    );

    // For right shift by >=1 (A < B), MSB of result is 0.
    check_msb_zero_after_right_shift: assert property (
        @(posedge CLK) ((A < B) && (shift_amount != 4'd0)) |-> (result[15] == 1'b0)
    );

    // Left shift by 15 when A > B produces {A[0], 15'b0}.
    check_left_shift_by_15: assert property (
        @(posedge CLK) ((A > B) && (shift_amount == 4'd15)) |-> (result == {A[0], 15'b0})
    );

    // Right shift by 15 when A < B produces {15'b0, B[15]}.
    check_right_shift_by_15: assert property (
        @(posedge CLK) ((A < B) && (shift_amount == 4'd15)) |-> (result == {15'b0, B[15]})
    );

    // For right shift case, result is less than or equal to B (unsigned).
    check_right_shift_monotonic: assert property (
        @(posedge CLK) (A < B) |-> (result <= B)
    );

endmodule