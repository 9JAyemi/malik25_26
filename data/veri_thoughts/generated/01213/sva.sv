module barrel_shifter_sva (
    input  logic        CLK,
    input  logic [7:0]  DATA,
    input  logic [2:0]  SHIFT_AMOUNT,
    input  logic        SHIFT_DIRECTION,
    input  logic [7:0]  SHIFTED_DATA
);

    // For SHIFT_DIRECTION=0, output equals DATA << SHIFT_AMOUNT.
    check_left_shift_correct: assert property (
        @(posedge CLK) (SHIFT_DIRECTION == 1'b0) |-> (SHIFTED_DATA == (DATA << SHIFT_AMOUNT))
    );

    // For SHIFT_DIRECTION=1, output equals DATA >> SHIFT_AMOUNT.
    check_right_shift_correct: assert property (
        @(posedge CLK) (SHIFT_DIRECTION == 1'b1) |-> (SHIFTED_DATA == (DATA >> SHIFT_AMOUNT))
    );

    // Shift amount 0 leaves data unchanged.
    check_shift_by_zero_identity: assert property (
        @(posedge CLK) (SHIFT_AMOUNT == 3'd0) |-> (SHIFTED_DATA == DATA)
    );

    // Left shift zero-fills lower bits.
    check_left_zero_fill_lsb: assert property (
        @(posedge CLK) (SHIFT_DIRECTION == 1'b0) |-> ((SHIFTED_DATA & ((8'h1 << SHIFT_AMOUNT) - 8'h1)) == 8'h00)
    );

    // Right shift zero-fills upper bits.
    check_right_zero_fill_msb: assert property (
        @(posedge CLK) (SHIFT_DIRECTION == 1'b1) |-> ((SHIFTED_DATA & ~(8'hFF >> SHIFT_AMOUNT)) == 8'h00)
    );

    // Output stable if all inputs stable.
    check_stable_with_stable_inputs: assert property (
        @(posedge CLK) $stable({DATA, SHIFT_AMOUNT, SHIFT_DIRECTION}) |-> $stable(SHIFTED_DATA)
    );

    // Zero input yields zero output.
    check_zero_input_zero_output: assert property (
        @(posedge CLK) (DATA == 8'h00) |-> (SHIFTED_DATA == 8'h00)
    );

    // Left shift by 7 moves bit0 to MSB and clears others.
    check_left_shift_by_seven: assert property (
        @(posedge CLK) (SHIFT_DIRECTION == 1'b0 && SHIFT_AMOUNT == 3'd7) |-> (SHIFTED_DATA == {DATA[0], 7'b0})
    );

    // Right shift by 7 moves MSB to LSB and clears others.
    check_right_shift_by_seven: assert property (
        @(posedge CLK) (SHIFT_DIRECTION == 1'b1 && SHIFT_AMOUNT == 3'd7) |-> (SHIFTED_DATA == {7'b0, DATA[7]})
    );

    // Output equals selected shift function for all cases.
    check_functional_equation: assert property (
        @(posedge CLK) SHIFTED_DATA == ((SHIFT_DIRECTION == 1'b0) ? (DATA << SHIFT_AMOUNT) : (DATA >> SHIFT_AMOUNT))
    );

endmodule