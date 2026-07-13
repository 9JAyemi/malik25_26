module barrel_shifter_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [1:0] shift_amt,
    input logic dir,
    input logic [3:0] out
);

// No RTL clock or reset; sample this combinational logic on clk.

    // shift_amt 00 passes the input through unchanged.
    check_shift_amt_00_passthrough: assert property (
        @(posedge clk) (shift_amt == 2'b00) |-> (out == in)
    );

// shift_amt 01 shifts left when dir==1.
    check_shift_amt_01_left: assert property (
        @(posedge clk) (shift_amt == 2'b01 && dir == 1'b1) |-> (out == {in[2:0], in[3]})
    );

// shift_amt 01 shifts right when dir==0.
    check_shift_amt_01_right: assert property (
        @(posedge clk) (shift_amt == 2'b01 && dir == 1'b0) |-> (out == {in[1:0], in[3:2]})
    );

// shift_amt 10 shifts left when dir==1.
    check_shift_amt_10_left: assert property (
        @(posedge clk) (shift_amt == 2'b10 && dir == 1'b1) |-> (out == {in[1:0], in[3:2]})
    );

// shift_amt 10 shifts right when dir==0.
    check_shift_amt_10_right: assert property (
        @(posedge clk) (shift_amt == 2'b10 && dir == 1'b0) |-> (out == {in[2:0], in[3]})
    );

// shift_amt 11 rotates left by one bit.
    check_shift_amt_11_rotate_left: assert property (
        @(posedge clk) (shift_amt == 2'b11) |-> (out == {in[0], in[3:1]})
    );

endmodule
