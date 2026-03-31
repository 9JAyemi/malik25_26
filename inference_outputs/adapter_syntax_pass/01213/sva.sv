module barrel_shifter_sva (
    input logic [7:0] DATA,
    input logic [2:0] SHIFT_AMOUNT,
    input logic SHIFT_DIRECTION,
    input logic [7:0] SHIFTED_DATA
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // In left-shift mode, SHIFTED_DATA must equal DATA shifted left by SHIFT_AMOUNT.
    check_left_shift_function: assert property (
        @($global_clock) (SHIFT_DIRECTION == 1'b0) |-> (SHIFTED_DATA == (DATA << SHIFT_AMOUNT))
    );

    // In right-shift mode, SHIFTED_DATA must equal DATA shifted right by SHIFT_AMOUNT.
    check_right_shift_function: assert property (
        @($global_clock) (SHIFT_DIRECTION == 1'b1) |-> (SHIFTED_DATA == (DATA >> SHIFT_AMOUNT))
    );

    // A zero shift amount must leave the data unchanged.
    check_zero_shift_passthrough: assert property (
        @($global_clock) (SHIFT_AMOUNT == 3'd0) |-> (SHIFTED_DATA == DATA)
    );

    // Left shifts must zero-fill the vacated low bits.
    check_left_shift_zero_fill: assert property (
        @($global_clock) (SHIFT_DIRECTION == 1'b0) && (SHIFT_AMOUNT != 3'd0) |-> (SHIFTED_DATA[7:SHIFT_AMOUNT] == 8'h00)
    );

    // Right shifts must zero-fill the vacated high bits.
    check_right_shift_zero_fill: assert property (
        @($global_clock) (SHIFT_DIRECTION == 1'b1) && (SHIFT_AMOUNT != 3'd0) |-> (SHIFTED_DATA[7:4] == 4'h0)
    );

    // A left shift by 8 must produce zero.
    check_left_shift_by_eight: assert property (
        @($global_clock) (SHIFT_DIRECTION == 1'b0) && (SHIFT_AMOUNT == 3'd8) |-> (SHIFTED_DATA == 8'h00)
    );

    // A right shift by 8 must produce zero.
    check_right_shift_by_eight: assert property (
        @($global_clock) (SHIFT_DIRECTION == 1'b1) && (SHIFT_AMOUNT == 3'd8) |-> (SHIFTED_DATA == 8'h00)
    );

endmodule