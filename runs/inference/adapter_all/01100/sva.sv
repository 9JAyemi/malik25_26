module Approx_adder_sva #(
    parameter W = 26,
    parameter LowL = 16
) (
    input logic add_sub,
    input logic [W-1:0] in1,
    input logic [W-1:0] in2,
    input logic [W:0] res
);

    // No RTL clock or reset; sample on the formal global clock.

    // In add mode, res matches the full signed addition result.
    check_add_mode_result: assert property (
        @($global_clock) (!add_sub) |-> (res == {1'b0, (in1 + in2)})
    );

    // In subtract mode, res matches the full signed subtraction result.
    check_sub_mode_result: assert property (
        @($global_clock) add_sub |-> (res == {1'b0, (in1 - in2)})
    );

    // In add mode, the upper bits of res come from the in1 upper bits.
    check_add_upper_bits: assert property (
        @($global_clock) (!add_sub) |-> (res[W-1:LowL] == in1[W-1:LowL])
    );

    // In subtract mode, the upper bits of res come from the in1 upper bits.
    check_sub_upper_bits: assert property (
        @($global_clock) add_sub |-> (res[W-1:LowL] == in1[W-1:LowL])
    );

    // In add mode, the lower bits of res come from the in1 lower bits.
    check_add_lower_bits: assert property (
        @($global_clock) (!add_sub) |-> (res[LowL-1:0] == in1[LowL-1:0])
    );

    // In subtract mode, the lower bits of res come from the in1 lower bits.
    check_sub_lower_bits: assert property (
        @($global_clock) add_sub |-> (res[LowL-1:0] == in1[LowL-1:0])
    );

    // In add mode, the MSB of res is always zero.
    check_add_msb_zero: assert property (
        @($global_clock) (!add_sub) |-> (res[W] == 1'b0)
    );

    // In subtract mode, the MSB of res is always zero.
    check_sub_msb_zero: assert property (
        @($global_clock) add_sub |-> (res[W] == 1'b0)
    );

    // Adding zero on in2 passes in1 through unchanged.
    check_add_zero_in2_passthrough: assert property (
        @($global_clock) (!add_sub && (in2 == '0)) |-> (res == {1'b0, in1})
    );

    // Subtracting zero on in2 passes in1 through unchanged.
    check_sub_zero_in2_passthrough: assert property (
        @($global_clock) (add_sub && (in2 == '0)) |-> (res == {1'b0, in1})
    );

    // Adding zero on in1 passes in2 through unchanged.
    check_add_zero_in1_passthrough: assert property (
        @($global_clock) (!add_sub && (in1 == '0)) |-> (res == {1'b0, in2})
    );

    // Subtracting equal operands yields zero.
    check_sub_equal_operands_zero: assert property (
        @($global_clock) (add_sub && (in1 == in2)) |-> (res == '0)
    );

endmodule