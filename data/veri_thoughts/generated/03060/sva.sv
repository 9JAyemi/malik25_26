module barrel_shifter_sva (
    input logic [7:0] DATA,
    input logic [2:0] SHIFT_AMOUNT,
    input logic       SHIFT_DIRECTION,
    input logic [7:0] SHIFTED_DATA
);

    // No clock or reset exists in the RTL; sample this combinational logic on $global_clock.

    // Left-shift mode must match DATA shifted left by SHIFT_AMOUNT.
    check_left_shift_result: assert property (
        @($global_clock)
        (SHIFT_DIRECTION == 1'b0) |-> (SHIFTED_DATA == (DATA << SHIFT_AMOUNT))
    );

    // Right-shift mode must match DATA shifted right by SHIFT_AMOUNT.
    check_right_shift_result: assert property (
        @($global_clock)
        (SHIFT_DIRECTION == 1'b1) |-> (SHIFTED_DATA == (DATA >> SHIFT_AMOUNT))
    );

    // A zero shift amount must pass DATA through unchanged.
    check_zero_shift_passthrough: assert property (
        @($global_clock)
        (SHIFT_AMOUNT == 3'd0) |-> (SHIFTED_DATA == DATA)
    );

    // Nonzero left shifts must zero-fill the vacated low bits.
    check_left_shift_zero_fill_low_bits: assert property (
        @($global_clock)
        (SHIFT_DIRECTION == 1'b0 && SHIFT_AMOUNT != 3'd0) |->
        ((SHIFTED_DATA & ((8'h01 << SHIFT_AMOUNT) - 8'h01)) == 8'h00)
    );

    // Nonzero right shifts must zero-fill the vacated high bits.
    check_right_shift_zero_fill_high_bits: assert property (
        @($global_clock)
        (SHIFT_DIRECTION == 1'b1 && SHIFT_AMOUNT != 3'd0) |->
        ((SHIFTED_DATA & ~(8'hFF >> SHIFT_AMOUNT)) == 8'h00)
    );

    // A left shift by seven keeps only DATA[0] in the MSB position.
    check_left_shift_by_seven: assert property (
        @($global_clock)
        (SHIFT_DIRECTION == 1'b0 && SHIFT_AMOUNT == 3'd7) |->
        (SHIFTED_DATA == {DATA[0], 7'b0})
    );

    // A right shift by seven keeps only DATA[7] in the LSB position.
    check_right_shift_by_seven: assert property (
        @($global_clock)
        (SHIFT_DIRECTION == 1'b1 && SHIFT_AMOUNT == 3'd7) |->
        (SHIFTED_DATA == {7'b0, DATA[7]})
    );

endmodule