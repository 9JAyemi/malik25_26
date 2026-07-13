module bitwise_xor_sva (
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] out
);
    // Combinational DUT with no clock/reset; sample on $global_clock and mask $initstate.

    // out equals bitwise XOR of a and b.
    check_out_is_xor: assert property (
        @($global_clock) disable iff ($initstate) (out == (a ^ b))
    );

    // If inputs are equal, out must be zero.
    check_zero_when_inputs_equal: assert property (
        @($global_clock) disable iff ($initstate) (a == b) |-> (out == 32'h0000_0000)
    );

    // If b is zero, out equals a.
    check_out_equals_a_when_b_zero: assert property (
        @($global_clock) disable iff ($initstate) (b == 32'h0000_0000) |-> (out == a)
    );

    // If a is zero, out equals b.
    check_out_equals_b_when_a_zero: assert property (
        @($global_clock) disable iff ($initstate) (a == 32'h0000_0000) |-> (out == b)
    );

    // If b is all ones, out equals bitwise NOT of a.
    check_out_is_invert_a_when_b_ones: assert property (
        @($global_clock) disable iff ($initstate) (b == 32'hFFFF_FFFF) |-> (out == ~a)
    );

    // If a is all ones, out equals bitwise NOT of b.
    check_out_is_invert_b_when_a_ones: assert property (
        @($global_clock) disable iff ($initstate) (a == 32'hFFFF_FFFF) |-> (out == ~b)
    );

    // XOR inverse: out ^ a equals b.
    check_inverse_property_with_a: assert property (
        @($global_clock) disable iff ($initstate) ((out ^ a) == b)
    );

    // XOR inverse: out ^ b equals a.
    check_inverse_property_with_b: assert property (
        @($global_clock) disable iff ($initstate) ((out ^ b) == a)
    );

    // If inputs are stable across a cycle, output must be stable.
    check_stability_when_inputs_stable: assert property (
        @($global_clock) disable iff ($initstate) ($stable(a) && $stable(b)) |-> $stable(out)
    );

    // If output changes, at least one input must have changed.
    check_output_change_requires_input_change: assert property (
        @($global_clock) disable iff ($initstate) (!$stable(out)) |-> (!$stable(a) || !$stable(b))
    );

endmodule