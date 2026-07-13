module barrel_shifter_sva (
    input logic clk,
    input logic [3:0] data_in,
    input logic [1:0] shift_amount,
    input logic [3:0] data_out
);

// No RTL reset; assertions are always active.

    // For shift_amount == 00, data_out equals data_in.
    check_no_shift_passthrough: assert property (
        @(posedge clk) (shift_amount == 2'b00) |-> (data_out == data_in)
    );

// For shift_amount == 01, data_out is a left rotate by 1.
    check_left_rotate_by_1: assert property (
        @(posedge clk) (shift_amount == 2'b01) |-> (data_out == {data_in[2:0], data_in[3]})
    );

// For shift_amount == 10, data_out is a left rotate by 2.
    check_left_rotate_by_2: assert property (
        @(posedge clk) (shift_amount == 2'b10) |-> (data_out == {data_in[1:0], data_in[3:2]})
    );

// For shift_amount == 11, data_out is a left rotate by 3.
    check_left_rotate_by_3: assert property (
        @(posedge clk) (shift_amount == 2'b11) |-> (data_out == {data_in[0], data_in[3:1]})
    );

endmodule
