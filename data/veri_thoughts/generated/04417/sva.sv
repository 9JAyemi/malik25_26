module barrel_shifter_sva (
    input logic       clk,
    input logic [3:0] data,
    input logic [1:0] shift_amount,
    input logic [3:0] result
);

    // shift_amount 00 passes data through unchanged.
    check_shift_0_passthrough: assert property (
        @(posedge clk) (shift_amount == 2'b00) |-> (result == data)
    );

    // shift_amount 01 shifts left by 1 with zero fill.
    check_shift_1_left_by_1: assert property (
        @(posedge clk) (shift_amount == 2'b01) |-> (result == {data[2:0], 1'b0})
    );

    // shift_amount 10 shifts left by 2 with zero fill.
    check_shift_2_left_by_2: assert property (
        @(posedge clk) (shift_amount == 2'b10) |-> (result == {data[1:0], 2'b00})
    );

    // shift_amount 11 shifts left by 3 with zero fill.
    check_shift_3_left_by_3: assert property (
        @(posedge clk) (shift_amount == 2'b11) |-> (result == {data[0], 3'b000})
    );

endmodule