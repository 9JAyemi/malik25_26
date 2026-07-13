module barrel_shifter_sva (
    input logic [15:0] in,
    input logic [3:0]  shift,
    input logic        dir,
    input logic [15:0] out
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // dir=0 selects left shift.
    check_left_shift: assert property (
        @($global_clock) (dir == 1'b0) |-> (out == (in << shift))
    );

    // dir=1 selects right shift.
    check_right_shift: assert property (
        @($global_clock) (dir == 1'b1) |-> (out == (in >> shift))
    );

    // A zero shift leaves the input unchanged.
    check_zero_shift_passthrough: assert property (
        @($global_clock) (shift == 4'd0) |-> (out == in)
    );

    // Left shift by 16 wraps the input to zero.
    check_left_shift_by_16: assert property (
        @($global_clock) ((dir == 1'b0) && (shift == 4'd16)) |-> (out == 16'h0000)
    );

    // Right shift by 16 wraps the input to zero.
    check_right_shift_by_16: assert property (
        @($global_clock) ((dir == 1'b1) && (shift == 4'd16)) |-> (out == 16'h0000)
    );

    // Left shift by 1 moves bit 0 into bit 1.
    check_left_shift_by_1: assert property (
        @($global_clock) ((dir == 1'b0) && (shift == 4'd1)) |-> (out == {in[14:0], 1'b0})
    );

    // Right shift by 1 moves bit 15 into bit 14.
    check_right_shift_by_1: assert property (
        @($global_clock) ((dir == 1'b1) && (shift == 4'd1)) |-> (out == {1'b0, in[15:1]})
    );

endmodule