module barrel_shifter_sva (
    input logic [3:0] data,
    input logic [1:0] shift_amount,
    input logic [3:0] result
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // shift_amount 00 passes data through unchanged.
    check_shift_00_passthrough: assert property (
        @($global_clock) (shift_amount == 2'b00) |-> (result == data)
    );

    // shift_amount 01 shifts left by 1 and inserts 0 in bit 0.
    check_shift_01_left1_zero: assert property (
        @($global_clock) (shift_amount == 2'b01) |-> (result == {data[2:0], 1'b0})
    );

    // shift_amount 10 shifts left by 2 and inserts 00 in bits 1:0.
    check_shift_10_left2_zero: assert property (
        @($global_clock) (shift_amount == 2'b10) |-> (result == {data[1:0], 2'b00})
    );

    // shift_amount 11 shifts left by 3 and inserts 000 in bits 2:0.
    check_shift_11_left3_zero: assert property (
        @($global_clock) (shift_amount == 2'b11) |-> (result == {data[0], 3'b000})
    );

endmodule