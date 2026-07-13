module top_module_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] shift_amt,
    input logic mode,
    input logic [3:0] out
);

    // No RTL clock or reset; sample combinational behavior on the global clock.

    // Equal inputs force the output to zero.
    check_equal_forces_zero: assert property (
        @($global_clock) (A == B) |-> (out == 4'b0000)
    );

    // With A larger than B, the output is the shifted larger value.
    check_signed_larger_shifts_a: assert property (
        @($global_clock) (($signed(A) > $signed(B)) && (A != B)) |-> (out == (A >> shift_amt))
    );

    // With A smaller than B, the output is the smaller value.
    check_signed_smaller_uses_a: assert property (
        @($global_clock) (($signed(A) < $signed(B)) && (A != B)) |-> (out == A)
    );

    // With A larger than B and mode high, the output is the logical right shift result.
    check_mode_high_logical_shift: assert property (
        @($global_clock) (($signed(A) > $signed(B)) && (A != B) && mode) |-> (out == (A >> shift_amt))
    );

    // With A larger than B and mode low, the output is the arithmetic right shift result.
    check_mode_low_arithmetic_shift: assert property (
        @($global_clock) (($signed(A) > $signed(B)) && (A != B) && !mode) |-> (out == ($signed(A) >>> shift_amt))
    );

    // With A smaller than B and mode high, the output is the logical right shift result.
    check_mode_high_logical_shift_when_a_smaller: assert property (
        @($global_clock) (($signed(A) < $signed(B)) && (A != B) && mode) |-> (out == (A >> shift_amt))
    );

    // With A smaller than B and mode low, the output is the logical right shift result.
    check_mode_low_logical_shift_when_a_smaller: assert property (
        @($global_clock) (($signed(A) < $signed(B)) && (A != B) && !mode) |-> (out == (A >> shift_amt))
    );

    // With A equal to zero and B larger than zero, the output is zero.
    check_zero_a_with_positive_b: assert property (
        @($global_clock) ((A == 4'b0000) && (B != 4'b0000) && ($signed(B) > $signed(A))) |-> (out == 4'b0000)
    );

    // With A equal to zero and B smaller than zero, the output is zero.
    check_zero_a_with_negative_b: assert property (
        @($global_clock) ((A == 4'b0000) && (B != 4'b0000) && ($signed(B) < $signed(A))) |-> (out == 4'b0000)
    );

    // With B equal to zero and A larger than zero, the output is zero.
    check_zero_b_with_positive_a: assert property (
        @($global_clock) ((B == 4'b0000) && (A != 4'b0000) && ($signed(A) > $signed(B))) |-> (out == 4'b0000)
    );

    // With B equal to zero and A smaller than zero, the output is zero.
    check_zero_b_with_negative_a: assert property (
        @($global_clock) ((B == 4'b0000) && (A != 4'b0000) && ($signed(A) < $signed(B))) |-> (out == 4'b0000)
    );

endmodule