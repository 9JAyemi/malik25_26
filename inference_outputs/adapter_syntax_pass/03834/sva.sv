module barrel_shifter_sva (
    input logic clk,
    input logic [3:0] D,
    input logic [1:0] A,
    input logic [3:0] S
);

    // A=00 passes D through unchanged.
    check_shift_00_passthrough: assert property (
        @(posedge clk) (A == 2'b00) |-> (S == D)
    );

    // A=01 shifts D left by one and inserts 0 in bit 0.
    check_shift_01_left1_zero: assert property (
        @(posedge clk) (A == 2'b01) |-> (S == {D[2:0], 1'b0})
    );

    // A=10 shifts D left by two and inserts 00 in bits [1:0].
    check_shift_10_left2_zero: assert property (
        @(posedge clk) (A == 2'b10) |-> (S == {D[1:0], 2'b00})
    );

    // A=11 shifts D left by three and inserts 000 in bits [2:0].
    check_shift_11_left3_zero: assert property (
        @(posedge clk) (A == 2'b11) |-> (S == {D[0], 3'b000})
    );

endmodule