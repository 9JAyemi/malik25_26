module top_module_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic enable,
    input logic [3:0] sum,
    input logic [3:0] diff,
    input logic [3:0] out
);

    // No explicit RTL clock or reset; sample this combinational logic on $global_clock.

    // sum is always the 4-bit addition of a and b.
    check_sum_matches_addition: assert property (
        @($global_clock) (sum == (a + b))
    );

    // diff[0] follows the implemented XOR-with-borrow equation when enabled.
    check_diff_bit0_matches_formula: assert property (
        @($global_clock) enable |-> (diff[0] == (a[0] ^ b[0] ^ (a[0] & ~b[0])))
    );

    // diff[1] uses the cumulative borrow term from bits 1:0 when enabled.
    check_diff_bit1_matches_formula: assert property (
        @($global_clock) enable |-> (
            diff[1] == (a[1] ^ b[1] ^ ((a[1] & ~b[1]) | (a[0] & ~b[0])))
        )
    );

    // diff[2] uses the cumulative borrow term from bits 2:0 when enabled.
    check_diff_bit2_matches_formula: assert property (
        @($global_clock) enable |-> (
            diff[2] == (a[2] ^ b[2] ^ ((a[2] & ~b[2]) | (a[1] & ~b[1]) | (a[0] & ~b[0])))
        )
    );

    // diff[3] uses the cumulative borrow term from bits 3:0 when enabled.
    check_diff_bit3_matches_formula: assert property (
        @($global_clock) enable |-> (
            diff[3] == (a[3] ^ b[3] ^ ((a[3] & ~b[3]) | (a[2] & ~b[2]) | (a[1] & ~b[1]) | (a[0] & ~b[0])))
        )
    );

    // The top-level output selects sum when enable is high.
    check_out_selects_sum_when_enabled: assert property (
        @($global_clock) enable |-> (out == sum)
    );

    // The top-level output matches the 4-bit addition result when enabled.
    check_out_matches_addition_when_enabled: assert property (
        @($global_clock) enable |-> (out == (a + b))
    );

    // Equal operands produce a zero diff when enabled.
    check_diff_zero_when_inputs_equal: assert property (
        @($global_clock) (enable && (a == b)) |-> (diff == 4'h0)
    );

    // A zero a operand makes diff equal to b when enabled.
    check_diff_matches_b_when_a_is_zero: assert property (
        @($global_clock) (enable && (a == 4'h0)) |-> (diff == b)
    );

    // A zero b operand makes the enabled output equal to a.
    check_out_matches_a_when_b_is_zero: assert property (
        @($global_clock) (enable && (b == 4'h0)) |-> (out == a)
    );

endmodule

bind top_module top_module_sva top_module_sva_inst (
    .a(a),
    .b(b),
    .enable(enable),
    .sum(sum),
    .diff(diff),
    .out(out)
);