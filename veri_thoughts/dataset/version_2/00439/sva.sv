module adder_mux_sva (
    input logic       clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       control,
    input logic [3:0] sum
);

    // Output must equal the 4-bit sum of a and b.
    check_sum_matches_four_bit_addition: assert property (
        @(posedge clk) (sum == (a + b))
    );

    // With control low, the selected path still produces a+b.
    check_control_low_matches_addition: assert property (
        @(posedge clk) (!control) |-> (sum == (a + b))
    );

    // With control high, the selected path still produces a+b.
    check_control_high_matches_addition: assert property (
        @(posedge clk) control |-> (sum == (a + b))
    );

    // Bit 0 follows the full-adder equation with cin tied low.
    check_lsb_matches_full_adder_equation: assert property (
        @(posedge clk) (sum[0] == (a[0] ^ b[0]))
    );

    // The low two bits match a 2-bit addition.
    check_low_two_bits_match_partial_addition: assert property (
        @(posedge clk) (sum[1:0] == (a[1:0] + b[1:0]))
    );

    // The low three bits match a 3-bit addition.
    check_low_three_bits_match_partial_addition: assert property (
        @(posedge clk) (sum[2:0] == (a[2:0] + b[2:0]))
    );

    // Adding zero on b preserves a.
    check_zero_b_passthrough: assert property (
        @(posedge clk) (b == 4'h0) |-> (sum == a)
    );

    // Adding zero on a preserves b.
    check_zero_a_passthrough: assert property (
        @(posedge clk) (a == 4'h0) |-> (sum == b)
    );

    // Toggling only control does not change the observed sum.
    check_control_toggle_does_not_change_sum: assert property (
        @(posedge clk) disable iff ($initstate)
        ($changed(control) && $stable(a) && $stable(b)) |-> $stable(sum)
    );

    // If all inputs are stable, the combinational output stays stable.
    check_stable_inputs_hold_sum: assert property (
        @(posedge clk) disable iff ($initstate)
        ($stable(a) && $stable(b) && $stable(control)) |-> $stable(sum)
    );

endmodule