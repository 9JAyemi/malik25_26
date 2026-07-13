module top_module_sva (
    input logic a1,
    input logic b1,
    input logic a2,
    input logic b2,
    input logic select,
    input logic [1:0] sum
);

    // No RTL clock or reset; sample combinational behavior on the global clock.

    // sum[0] is the XOR of the two half-adder sum bits.
    check_sum0_is_half_adder_xor: assert property (
        @($global_clock) sum[0] == (a1 ^ b1 ^ a2 ^ b2)
    );

    // sum[1] is the carry-out of the selected half adder.
    check_sum1_is_selected_half_adder_carry: assert property (
        @($global_clock) sum[1] == (select ? (a2 & b2) : (a1 & b1))
    );

    // With select low, sum matches the full expression using the first half adder carry.
    check_select_low_full_expression: assert property (
        @($global_clock) (!select) |-> (sum == {((a1 & b1) | (a2 & b2)), (a1 ^ b1 ^ a2 ^ b2)})
    );

    // With select high, sum matches the full expression using the second half adder carry.
    check_select_high_full_expression: assert property (
        @($global_clock) select |-> (sum == {((a2 & b2) | (a1 & b1)), (a1 ^ b1 ^ a2 ^ b2)})
    );

    // With select low, the carry-out bit is the AND of the two half-adder carries.
    check_select_low_carry_out: assert property (
        @($global_clock) (!select) |-> (sum[1] == ((a1 & b1) | (a2 & b2)))
    );

    // With select high, the carry-out bit is the AND of the two half-adder carries.
    check_select_high_carry_out: assert property (
        @($global_clock) select |-> (sum[1] == ((a1 & b1) | (a2 & b2)))
    );

    // With select low, the sum bit is the XOR of the two half-adder sum bits.
    check_select_low_sum_bit: assert property (
        @($global_clock) (!select) |-> (sum[0] == (a1 ^ b1 ^ a2 ^ b2))
    );

    // With select high, the sum bit is the XOR of the two half-adder sum bits.
    check_select_high_sum_bit: assert property (
        @($global_clock) select |-> (sum[0] == (a1 ^ b1 ^ a2 ^ b2))
    );

    // If both half-adder carries are low, the output is zero.
    check_both_carry_low_zero_output: assert property (
        @($global_clock) (!(a1 & b1) && !(a2 & b2)) |-> (sum == 2'b00)
    );

    // If both half-adder carries are high, the output is 2'b11.
    check_both_carry_high_one_output: assert property (
        @($global_clock) ((a1 & b1) && (a2 & b2)) |-> (sum == 2'b11)
    );

    // If only the first half-adder carry is high, the output is 2'b10.
    check_first_carry_only_output: assert property (
        @($global_clock) ((a1 & b1) && !(a2 & b2)) |-> (sum == 2'b10)
    );

    // If only the second half-adder carry is high, the output is 2'b10.
    check_second_carry_only_output: assert property (
        @($global_clock) (!(a1 & b1) && (a2 & b2)) |-> (sum == 2'b10)
    );

endmodule