module top_module_sva (
    input logic a,
    input logic b,
    input logic [2:0] a_bitwise,
    input logic [2:0] b_bitwise,
    input logic [2:0] out_sum
);

    // No RTL clock or reset; sample combinational behavior on the global clock.

    // out_sum matches the half-adder sum plus the bitwise OR result.
    check_out_sum_function: assert property (
        @($global_clock)
        out_sum == ((a ^ b) + (a_bitwise | b_bitwise))
    );

    // With a and b low, the half-adder sum is zero.
    check_zero_inputs_sum: assert property (
        @($global_clock)
        (!a && !b) |-> (out_sum == (a_bitwise | b_bitwise))
    );

    // With a and b high, the half-adder sum is one.
    check_one_inputs_sum: assert property (
        @($global_clock)
        (a && b) |-> (out_sum == (a_bitwise | b_bitwise) + 3'd1)
    );

    // With a low and b high, the half-adder sum is one.
    check_a_low_b_high_sum: assert property (
        @($global_clock)
        (!a && b) |-> (out_sum == (a_bitwise | b_bitwise) + 3'd1)
    );

    // With a high and b low, the half-adder sum is one.
    check_a_high_b_low_sum: assert property (
        @($global_clock)
        (a && !b) |-> (out_sum == (a_bitwise | b_bitwise) + 3'd1)
    );

    // If the bitwise OR result is zero, out_sum reduces to the half-adder sum.
    check_zero_or_result: assert property (
        @($global_clock)
        ((a_bitwise | b_bitwise) == 3'b000) |-> (out_sum == (a ^ b))
    );

    // If the half-adder sum is zero, out_sum reduces to the bitwise OR result.
    check_zero_sum_result: assert property (
        @($global_clock)
        ((a ^ b) == 1'b0) |-> (out_sum == (a_bitwise | b_bitwise))
    );

    // If the half-adder sum is one, out_sum increments the bitwise OR result by one.
    check_one_sum_result: assert property (
        @($global_clock)
        ((a ^ b) == 1'b1) |-> (out_sum == (a_bitwise | b_bitwise) + 3'd1)
    );

    // With a and b low, out_sum is the bitwise OR result.
    check_zero_inputs_final: assert property (
        @($global_clock)
        (!a && !b) |-> (out_sum == (a_bitwise | b_bitwise))
    );

    // With a and b high, out_sum is the bitwise OR result plus one.
    check_one_inputs_final: assert property (
        @($global_clock)
        (a && b) |-> (out_sum == (a_bitwise | b_bitwise) + 3'd1)
    );

    // With a low and b high, out_sum is the bitwise OR result plus one.
    check_a_low_b_high_final: assert property (
        @($global_clock)
        (!a && b) |-> (out_sum == (a_bitwise | b_bitwise) + 3'd1)
    );

    // With a high and b low, out_sum is the bitwise OR result plus one.
    check_a_high_b_low_final: assert property (
        @($global_clock)
        (a && !b) |-> (out_sum == (a_bitwise | b_bitwise) + 3'd1)
    );

endmodule