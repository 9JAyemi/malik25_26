module multiplier_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic enable,
    input logic signed [7:0] result
);
    // No explicit clock/reset in RTL; sample assertions on $global_clock. Purely combinational behavior.

    // When enabled, result equals the signed product of a and b.
    check_enabled_product: assert property (
        @(posedge $global_clock) enable |-> (result == ($signed(a) * $signed(b)))
    );

    // When disabled, result is 0.
    check_disabled_zero: assert property (
        @(posedge $global_clock) !enable |-> (result == 8'sd0)
    );

    // If either operand is zero while enabled, result is zero.
    check_zero_operand_zero_result: assert property (
        @(posedge $global_clock) (enable && ((a == 4'sd0) || (b == 4'sd0))) |-> (result == 8'sd0)
    );

    // If both operands are non-zero while enabled, result is non-zero.
    check_nonzero_operands_nonzero_result: assert property (
        @(posedge $global_clock) (enable && (a != 4'sd0) && (b != 4'sd0)) |-> (result != 8'sd0)
    );

    // With mixed operand signs (and non-zero), the product sign is negative.
    check_negative_sign_for_mixed_signs: assert property (
        @(posedge $global_clock) (enable && (a != 4'sd0) && (b != 4'sd0) && (a[3] ^ b[3])) |-> (result[7] == 1'b1)
    );

    // With same operand signs (and non-zero), the product sign is non-negative.
    check_positive_sign_for_same_signs: assert property (
        @(posedge $global_clock) (enable && (a != 4'sd0) && (b != 4'sd0) && ~(a[3] ^ b[3])) |-> (result[7] == 1'b0)
    );

    // Output remains stable when inputs and enable are stable.
    check_output_stable_if_inputs_stable: assert property (
        @(posedge $global_clock) ($stable(a) && $stable(b) && $stable(enable)) |-> $stable(result)
    );

    // Known inputs yield a known output (no X/Z propagation beyond inputs).
    check_known_output_when_inputs_known: assert property (
        @(posedge $global_clock) (!$isunknown({enable, a, b})) |-> (!$isunknown(result))
    );
endmodule