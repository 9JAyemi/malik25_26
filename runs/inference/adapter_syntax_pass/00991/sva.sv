module barrel_shifter_sva (
    input logic clk,
    input logic [3:0] data_in,
    input logic [1:0] shift_amount,
    input logic [3:0] data_out
);

    // No RTL clock or reset; clk is a sampling clock for these checks.

    // shift_amount 00 passes data_in[0] to data_out[0].
    check_shift00_bit0: assert property (
        @(posedge clk) (shift_amount == 2'b00) |-> (data_out[0] == data_in[0])
    );

    // shift_amount 00 passes data_in[1] to data_out[1].
    check_shift00_bit1: assert property (
        @(posedge clk) (shift_amount == 2'b00) |-> (data_out[1] == data_in[1])
    );

    // shift_amount 00 passes data_in[2] to data_out[2].
    check_shift00_bit2: assert property (
        @(posedge clk) (shift_amount == 2'b00) |-> (data_out[2] == data_in[2])
    );

    // shift_amount 00 passes data_in[3] to data_out[3].
    check_shift00_bit3: assert property (
        @(posedge clk) (shift_amount == 2'b00) |-> (data_out[3] == data_in[3])
    );

    // shift_amount 01 rotates the input left by one bit.
    check_shift01_rotation: assert property (
        @(posedge clk) (shift_amount == 2'b01) |-> (data_out == {data_in[2:0], data_in[3]})
    );

    // shift_amount 10 rotates the input left by two bits.
    check_shift10_rotation: assert property (
        @(posedge clk) (shift_amount == 2'b10) |-> (data_out == {data_in[1:0], data_in[3:2]})
    );

    // shift_amount 11 passes data_in[3] to data_out[0].
    check_shift11_bit0: assert property (
        @(posedge clk) (shift_amount == 2'b11) |-> (data_out[0] == data_in[3])
    );

    // shift_amount 11 passes data_in[2] to data_out[1].
    check_shift11_bit1: assert property (
        @(posedge clk) (shift_amount == 2'b11) |-> (data_out[1] == data_in[2])
    );

    // shift_amount 11 passes data_in[1] to data_out[2].
    check_shift11_bit2: assert property (
        @(posedge clk) (shift_amount == 2'b11) |-> (data_out[2] == data_in[1])
    );

    // shift_amount 11 passes data_in[0] to data_out[3].
    check_shift11_bit3: assert property (
        @(posedge clk) (shift_amount == 2'b11) |-> (data_out[3] == data_in[0])
    );

endmodule