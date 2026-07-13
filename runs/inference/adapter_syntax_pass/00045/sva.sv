module top_module_sva (
    input logic a,
    input logic b,
    input logic [2:0] a_bitwise,
    input logic [2:0] b_bitwise,
    input logic [2:0] out_sum
);

    // No RTL clock or reset; sample combinational behavior on the formal global clock.

    // out_sum must equal the half-adder sum of a and b.
    check_out_sum_matches_half_adder_sum: assert property (
        @($global_clock) out_sum == (a ^ b)
    );

    // out_sum[0] must match the half-adder sum bit.
    check_out_sum_bit0_matches_half_adder: assert property (
        @($global_clock) out_sum[0] == (a ^ b)
    );

    // out_sum[1] must be zero because the RTL does not drive bit 1.
    check_out_sum_bit1_zero: assert property (
        @($global_clock) out_sum[1] == 1'b0
    );

    // out_sum[2] must be zero because the RTL does not drive bit 2.
    check_out_sum_bit2_zero: assert property (
        @($global_clock) out_sum[2] == 1'b0
    );

    // Equal inputs must produce a zero sum.
    check_equal_inputs_zero_sum: assert property (
        @($global_clock) (a == b) |-> (out_sum == 3'b000)
    );

    // Different inputs must produce a one-hot sum.
    check_different_inputs_onehot_sum: assert property (
        @($global_clock) (a != b) |-> (out_sum == 3'b001)
    );

endmodule