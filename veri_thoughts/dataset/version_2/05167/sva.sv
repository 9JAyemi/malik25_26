module Bit_Shifting_Operators_sva (
    input logic        clk,
    input logic [31:0] in,
    input logic [4:0]  shift,
    input logic [31:0] out_l,
    input logic [31:0] out_r,
    input logic [31:0] out_a
);

    // No RTL clock/reset; sample the combinational outputs on an external clock.

    // out_l must match the RTL left-shift expression.
    check_left_shift_value: assert property (
        @(posedge clk) out_l == (in << shift)
    );

    // out_r must match the RTL right-shift expression.
    check_right_shift_value: assert property (
        @(posedge clk) out_r == (in >> shift)
    );

    // out_a must match the RTL conditional expression exactly.
    check_conditional_a_value: assert property (
        @(posedge clk) out_a == ((in[31] == 1'b0) ? (in >> shift) : (({32{in[31]}} >> shift) | (in >> shift)))
    );

    // With MSB clear, out_a must equal the logical right shift.
    check_a_matches_right_shift_when_msb_zero: assert property (
        @(posedge clk) (in[31] == 1'b0) |-> (out_a == out_r)
    );

    // With MSB set, out_a must follow the RTL mask-and-OR branch.
    check_a_mask_branch_when_msb_one: assert property (
        @(posedge clk) (in[31] == 1'b1) |-> (out_a == ((32'hFFFF_FFFF >> shift) | out_r))
    );

    // A zero shift must pass in through to out_l and out_r.
    check_zero_shift_passthrough_lr: assert property (
        @(posedge clk) (shift == 5'd0) |-> ((out_l == in) && (out_r == in))
    );

    // A zero shift with MSB clear must pass in through to out_a.
    check_zero_shift_passthrough_a_when_msb_zero: assert property (
        @(posedge clk) ((shift == 5'd0) && (in[31] == 1'b0)) |-> (out_a == in)
    );

    // A zero shift with MSB set must drive out_a to all ones per the RTL.
    check_zero_shift_a_all_ones_when_msb_one: assert property (
        @(posedge clk) ((shift == 5'd0) && (in[31] == 1'b1)) |-> (out_a == 32'hFFFF_FFFF)
    );

    // A shift of 31 must leave only the original MSB in out_r bit 0.
    check_max_shift_right_shape: assert property (
        @(posedge clk) (shift == 5'd31) |-> (out_r == {31'b0, in[31]})
    );

    // A shift of 31 must leave only the original LSB in out_l bit 31.
    check_max_shift_left_shape: assert property (
        @(posedge clk) (shift == 5'd31) |-> (out_l == {in[0], 31'b0})
    );

endmodule