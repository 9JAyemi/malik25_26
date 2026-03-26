module bitwise_shifter_sva (
    input logic clk,
    input logic [31:0] in,
    input logic [1:0] shift,
    input logic [31:0] out
);

    // shift=00 passes the input through unchanged.
    check_shift_00_passthrough: assert property (
        @(posedge clk) (shift == 2'b00) |-> (out == in)
    );

    // shift=01 shifts left by one and inserts zero into bit 0.
    check_shift_01_left_by_one: assert property (
        @(posedge clk) (shift == 2'b01) |-> (out == {in[30:0], 1'b0})
    );

    // shift=10 shifts right by one and inserts zero into bit 31.
    check_shift_10_right_by_one: assert property (
        @(posedge clk) (shift == 2'b10) |-> (out == {1'b0, in[31:1]})
    );

    // shift=11 shifts right by two and inserts zeros into bits 31:30.
    check_shift_11_right_by_two: assert property (
        @(posedge clk) (shift == 2'b11) |-> (out == {2'b00, in[31:2]})
    );

endmodule