module barrel_shifter_sva (
    input logic [15:0] data_in,
    input logic [3:0]  shift_amount,
    input logic        shift_direction,
    input logic [15:0] data_out
);

    // Left shift mode computes data_out as data_in shifted left.
    check_left_shift_function: assert property (
        @($global_clock)
        (shift_direction == 1'b1) |-> (data_out == (data_in << shift_amount))
    );

    // Right shift mode computes data_out as data_in shifted right.
    check_right_shift_function: assert property (
        @($global_clock)
        (shift_direction == 1'b0) |-> (data_out == (data_in >> shift_amount))
    );

    // A zero shift passes data_in through unchanged.
    check_zero_shift_passthrough: assert property (
        @($global_clock)
        (shift_amount == 4'd0) |-> (data_out == data_in)
    );

    // Left shifts fill the vacated low bits with zeros.
    check_left_shift_zero_fill_lsb: assert property (
        @($global_clock)
        (shift_direction == 1'b1) && (shift_amount > 4'd0)
        |-> ((data_out & ((16'h0001 << shift_amount) - 16'h0001)) == 16'h0000)
    );

    // Right shifts fill the vacated high bits with zeros.
    check_right_shift_zero_fill_msb: assert property (
        @($global_clock)
        (shift_direction == 1'b0) && (shift_amount > 4'd0)
        |-> ((data_out & ~(16'hFFFF >> shift_amount)) == 16'h0000)
    );

    // A left shift by 15 moves bit 0 to bit 15 and clears the rest.
    check_left_shift_by_15: assert property (
        @($global_clock)
        (shift_direction == 1'b1) && (shift_amount == 4'd15)
        |-> (data_out == {data_in[0], 15'b0})
    );

    // A right shift by 15 moves bit 15 to bit 0 and clears the rest.
    check_right_shift_by_15: assert property (
        @($global_clock)
        (shift_direction == 1'b0) && (shift_amount == 4'd15)
        |-> (data_out == {15'b0, data_in[15]})
    );

endmodule