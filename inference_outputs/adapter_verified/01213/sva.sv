module barrel_shifter_sva (
    input logic CLK,
    input logic [7:0] DATA,
    input logic [2:0] SHIFT_AMOUNT,
    input logic SHIFT_DIRECTION,
    input logic [7:0] SHIFTED_DATA
);

// No reset in RTL; sample combinational behavior on CLK.

    // When SHIFT_DIRECTION==0, output equals DATA shifted left by SHIFT_AMOUNT.
    check_left_shift_function: assert property (
        @(posedge CLK) (SHIFT_DIRECTION == 1'b0) |-> (SHIFTED_DATA == (DATA << SHIFT_AMOUNT))
    );

// When SHIFT_DIRECTION==1, output equals DATA shifted right by SHIFT_AMOUNT.
    check_right_shift_function: assert property (
        @(posedge CLK) (SHIFT_DIRECTION == 1'b1) |-> (SHIFTED_DATA == (DATA >> SHIFT_AMOUNT))
    );

// Left shift by 0 returns the input unchanged.
    check_left_shift_zero: assert property (
        @(posedge CLK) (SHIFT_DIRECTION == 1'b0 && SHIFT_AMOUNT == 3'd0) |-> (SHIFTED_DATA == DATA)
    );

// Right shift by 0 returns the input unchanged.
    check_right_shift_zero: assert property (
        @(posedge CLK) (SHIFT_DIRECTION == 1'b1 && SHIFT_AMOUNT == 3'd0) |-> (SHIFTED_DATA == DATA)
    );

// Left shift by 1 inserts a zero into the LSB.
    check_left_shift_one: assert property (
        @(posedge CLK) (SHIFT_DIRECTION == 1'b0 && SHIFT_AMOUNT == 3'd1) |-> (SHIFTED_DATA == {DATA[6:0], 1'b0})
    );

// Right shift by 1 inserts a zero into the MSB.
    check_right_shift_one: assert property (
        @(posedge CLK) (SHIFT_DIRECTION == 1'b1 && SHIFT_AMOUNT == 3'd1) |-> (SHIFTED_DATA == {1'b0, DATA[7:1]})
    );

// Left shift by 7 moves the MSB into the LSB.
    check_left_shift_seven: assert property (
        @(posedge CLK) (SHIFT_DIRECTION == 1'b0 && SHIFT_AMOUNT == 3'd7) |-> (SHIFTED_DATA == {DATA[0], DATA[7:1]})
    );

// Right shift by 7 moves the LSB into the MSB.
    check_right_shift_seven: assert property (
        @(posedge CLK) (SHIFT_DIRECTION == 1'b1 && SHIFT_AMOUNT == 3'd7) |-> (SHIFTED_DATA == {DATA[7], DATA[6:0]})
    );

endmodule
