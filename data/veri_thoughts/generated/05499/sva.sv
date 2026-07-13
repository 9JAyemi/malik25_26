module data_manipulation_sva (
    input logic clk,
    input logic [3:0] in_data,
    input logic [1:0] ctrl,
    input logic [3:0] out_data
);

    // Combinational RTL with no native clock or reset; clk is a sampling clock.

    // ctrl=00 inverts all input bits.
    check_invert_mode: assert property (
        @(posedge clk) (ctrl == 2'b00) |-> (out_data == ~in_data)
    );

    // ctrl=01 computes the two's complement of the input.
    check_twos_complement_mode: assert property (
        @(posedge clk) (ctrl == 2'b01) |-> (out_data == (~in_data + 4'b0001))
    );

    // ctrl=10 shifts left by one and inserts zero at the LSB.
    check_left_shift_mode: assert property (
        @(posedge clk) (ctrl == 2'b10) |-> (out_data == {in_data[2:0], 1'b0})
    );

    // ctrl=11 shifts right by one and inserts zero at the MSB.
    check_right_shift_mode: assert property (
        @(posedge clk) (ctrl == 2'b11) |-> (out_data == {1'b0, in_data[3:1]})
    );

endmodule