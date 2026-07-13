module Approx_adder_sva
    #(parameter W=26, parameter LowL=16) (
        input logic add_sub,
        input logic [W-1:0] in1,
        input logic [W-1:0] in2,
        input logic [W:0] res
    );

    // No RTL clock or reset; sample combinational behavior on the formal global clock.

    // In add mode, res must equal the 27-bit sum of in1 and in2.
    check_add_mode_sum: assert property (
        @($global_clock) (add_sub == 1'b0) |-> (res == {1'b0, (in1 + in2)})
    );

    // In subtract mode, res must equal the 27-bit difference of in1 and in2.
    check_sub_mode_difference: assert property (
        @($global_clock) (add_sub == 1'b1) |-> (res == {1'b0, (in1 - in2)})
    );

    // In add mode, the upper bit of res must be zero.
    check_add_mode_upper_zero: assert property (
        @($global_clock) (add_sub == 1'b0) |-> (res[W] == 1'b0)
    );

    // In subtract mode, the upper bit of res must be zero.
    check_sub_mode_upper_zero: assert property (
        @($global_clock) (add_sub == 1'b1) |-> (res[W] == 1'b0)
    );

    // In add mode, the lower LowL bits of res must match the lower LowL bits of in1.
    check_add_mode_lower_bits_match_in1: assert property (
        @($global_clock) (add_sub == 1'b0) |-> (res[LowL-1:0] == in1[LowL-1:0])
    );

    // In subtract mode, the lower LowL bits of res must match the lower LowL bits of in1.
    check_sub_mode_lower_bits_match_in1: assert property (
        @($global_clock) (add_sub == 1'b1) |-> (res[LowL-1:0] == in1[LowL-1:0])
    );

    // In add mode, the upper W-LowL bits of res must match the upper W-LowL bits of in1.
    check_add_mode_upper_bits_match_in1: assert property (
        @($global_clock) (add_sub == 1'b0) |-> (res[W-1:LowL] == in1[W-1:LowL])
    );

    // In subtract mode, the upper W-LowL bits of res must match the upper W-LowL bits of in1.
    check_sub_mode_upper_bits_match_in1: assert property (
        @($global_clock) (add_sub == 1'b1) |-> (res[W-1:LowL] == in1[W-1:LowL])
    );

endmodule