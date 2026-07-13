module barrel_shifter_sva (
    input logic [7:0] DATA,
    input logic [2:0] SHIFT_AMOUNT,
    input logic SHIFT_DIRECTION,
    input logic [7:0] SHIFTED_DATA
);

    // No RTL clock or reset; sample on the formal global clock.

    // Left shift mode must produce the left-shifted result.
    check_left_shift_result: assert property (
        @($global_clock) (SHIFT_DIRECTION == 1'b0) |-> (SHIFTED_DATA == (DATA << SHIFT_AMOUNT))
    );

    // Right shift mode must produce the right-shifted result.
    check_right_shift_result: assert property (
        @($global_clock) (SHIFT_DIRECTION == 1'b1) |-> (SHIFTED_DATA == (DATA >> SHIFT_AMOUNT))
    );

    // A zero shift amount must pass the data through unchanged.
    check_zero_shift_passthrough: assert property (
        @($global_clock) (SHIFT_AMOUNT == 3'd0) |-> (SHIFTED_DATA == DATA)
    );

    // Left shift by 8 must zero the output.
    check_left_shift_by_eight: assert property (
        @($global_clock) (SHIFT_DIRECTION == 1'b0 && SHIFT_AMOUNT == 3'd8) |-> (SHIFTED_DATA == 8'h00)
    );

    // Right shift by 8 must zero the output.
    check_right_shift_by_eight: assert property (
        @($global_clock) (SHIFT_DIRECTION == 1'b1 && SHIFT_AMOUNT == 3'd8) |-> (SHIFTED_DATA == 8'h00)
    );

    // Left shift by 7 must leave only bit 0 in the MSB position.
    check_left_shift_by_seven: assert property (
        @($global_clock) (SHIFT_DIRECTION == 1'b0 && SHIFT_AMOUNT == 3'd7) |-> (SHIFTED_DATA == {DATA[0], 7'b0})
    );

    // Right shift by 7 must leave only the MSB in bit 0.
    check_right_shift_by_seven: assert property (
        @($global_clock) (SHIFT_DIRECTION == 1'b1 && SHIFT_AMOUNT == 3'd7) |-> (SHIFTED_DATA == {DATA[7], 7'b0})
    );

    // Left shift by 1 must move bits 0 through 6 up by one.
    check_left_shift_by_one: assert property (
        @($global_clock) (SHIFT_DIRECTION == 1'b0 && SHIFT_AMOUNT == 3'd1) |-> (SHIFTED_DATA == {DATA[6:0], 1'b0})
    );

    // Right shift by 1 must move bits 1 through 7 down by one.
    check_right_shift_by_one: assert property (
        @($global_clock) (SHIFT_DIRECTION == 1'b1 && SHIFT_AMOUNT == 3'd1) |-> (SHIFTED_DATA == {1'b0, DATA[7:1]})
    );

endmodule