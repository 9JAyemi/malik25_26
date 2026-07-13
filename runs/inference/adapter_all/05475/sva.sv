module barrel_shifter_sva (
    input logic [3:0] in,
    input logic [1:0] shift_amt,
    input logic dir,
    input logic [3:0] out
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // shift_amt 00 passes the input through unchanged.
    check_shift_amt_00_passthrough: assert property (
        @($global_clock) (shift_amt == 2'b00) |-> (out == in)
    );

    // shift_amt 01 with dir=0 rotates left by 1 bit.
    check_shift_amt_01_dir0_rotate_left: assert property (
        @($global_clock) (shift_amt == 2'b01 && dir == 1'b0) |-> (out == {in[2:0], in[3]})
    );

    // shift_amt 01 with dir=1 rotates right by 1 bit.
    check_shift_amt_01_dir1_rotate_right: assert property (
        @($global_clock) (shift_amt == 2'b01 && dir == 1'b1) |-> (out == {in[1:0], in[3:2]})
    );

    // shift_amt 10 with dir=0 rotates left by 2 bits.
    check_shift_amt_10_dir0_rotate_left: assert property (
        @($global_clock) (shift_amt == 2'b10 && dir == 1'b0) |-> (out == {in[1:0], in[3:2]})
    );

    // shift_amt 10 with dir=1 rotates right by 2 bits.
    check_shift_amt_10_dir1_rotate_right: assert property (
        @($global_clock) (shift_amt == 2'b10 && dir == 1'b1) |-> (out == {in[2:0], in[3]})
    );

    // shift_amt 11 swaps the input bits.
    check_shift_amt_11_swap: assert property (
        @($global_clock) (shift_amt == 2'b11) |-> (out == {in[0], in[3:1]})
    );

endmodule