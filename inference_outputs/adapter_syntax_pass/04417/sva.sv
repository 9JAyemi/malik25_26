module barrel_shifter_sva (
    input logic clk,
    input logic [3:0] data,
    input logic [1:0] shift_amount,
    input logic [3:0] result
);

    // No RTL clock or reset; clk is a sampling clock for these checks.

    // shift_amount 00 passes data through unchanged.
    check_shift_00_passthrough: assert property (
        @(posedge clk) (shift_amount == 2'b00) |-> (result == data)
    );

    // shift_amount 01 shifts data left by one and inserts 0 in bit 0.
    check_shift_01_left_by_one: assert property (
        @(posedge clk) (shift_amount == 2'b01) |-> (result == {data[2:0], 1'b0})
    );

    // shift_amount 10 shifts data left by two and inserts 00 in bits [1:0].
    check_shift_10_left_by_two: assert property (
        @(posedge clk) (shift_amount == 2'b10) |-> (result == {data[1:0], 2'b00})
    );

    // shift_amount 11 shifts data left by three and inserts 000 in bits [2:0].
    check_shift_11_left_by_three: assert property (
        @(posedge clk) (shift_amount == 2'b11) |-> (result == {data[0], 3'b000})
    );

endmodule