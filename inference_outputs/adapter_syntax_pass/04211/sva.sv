module barrel_shifter_sva (
    input logic [15:0] in,
    input logic [3:0]  shift_amt,
    input logic        shift_left,
    input logic [15:0] out
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // Left shift mode must produce the left-shifted input.
    check_left_shift_result: assert property (
        @($global_clock) shift_left |-> (out == (in << shift_amt))
    );

    // Right shift mode must produce the right-shifted input.
    check_right_shift_result: assert property (
        @($global_clock) !shift_left |-> (out == (in >> shift_amt))
    );

    // A zero shift amount must pass the input through unchanged.
    check_zero_shift_passthrough: assert property (
        @($global_clock) (shift_amt == 4'd0) |-> (out == in)
    );

    // Left shifts must zero-fill the vacated low bits.
    check_left_shift_zero_fill: assert property (
        @($global_clock) shift_left |-> ((out & ((16'h0001 << shift_amt) - 16'h0001)) == 16'h0000)
    );

    // Right shifts must zero-fill the vacated high bits.
    check_right_shift_zero_fill: assert property (
        @($global_clock) !shift_left |-> ((out & ~(16'hFFFF >> shift_amt)) == 16'h0000)
    );

    // Left shifts must not change the upper bits beyond the shift amount.
    check_left_shift_upper_bound: assert property (
        @($global_clock) shift_left |-> ((out & ~(16'hFFFF << shift_amt)) == (in & ~(16'hFFFF << shift_amt)))
    );

    // Right shifts must not change the lower bits beyond the shift amount.
    check_right_shift_lower_bound: assert property (
        @($global_clock) !shift_left |-> ((out & (16'hFFFF >> shift_amt)) == (in & (16'hFFFF >> shift_amt)))
    );

endmodule