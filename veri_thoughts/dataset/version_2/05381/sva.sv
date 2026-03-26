module barrel_shifter_sva (
    input logic clk,
    input logic [7:0] in,
    input logic [2:0] shift_amt,
    input logic [7:0] out
);

    // External sampling clock; RTL itself is combinational and has no reset.

    // shift_amt 000 passes input through unchanged.
    check_no_shift: assert property (
        @(posedge clk) (shift_amt == 3'b000) |-> (out == in)
    );

    // shift_amt 001 shifts left by 1 and fills LSB with 0.
    check_shift_left_1: assert property (
        @(posedge clk) (shift_amt == 3'b001) |-> (out == {in[6:0], 1'b0})
    );

    // shift_amt 010 shifts left by 2 and fills low bits with 0.
    check_shift_left_2: assert property (
        @(posedge clk) (shift_amt == 3'b010) |-> (out == {in[5:0], 2'b00})
    );

    // shift_amt 011 shifts left by 3 and fills low bits with 0.
    check_shift_left_3: assert property (
        @(posedge clk) (shift_amt == 3'b011) |-> (out == {in[4:0], 3'b000})
    );

    // shift_amt 100 shifts left by 4 and fills low bits with 0.
    check_shift_left_4: assert property (
        @(posedge clk) (shift_amt == 3'b100) |-> (out == {in[3:0], 4'b0000})
    );

    // shift_amt 101 shifts right by 1 and fills MSB with 0.
    check_shift_right_1: assert property (
        @(posedge clk) (shift_amt == 3'b101) |-> (out == {1'b0, in[7:1]})
    );

    // shift_amt 110 shifts right by 2 and fills high bits with 0.
    check_shift_right_2: assert property (
        @(posedge clk) (shift_amt == 3'b110) |-> (out == {2'b00, in[7:2]})
    );

    // shift_amt 111 shifts right by 3 and fills high bits with 0.
    check_shift_right_3: assert property (
        @(posedge clk) (shift_amt == 3'b111) |-> (out == {3'b000, in[7:3]})
    );

endmodule