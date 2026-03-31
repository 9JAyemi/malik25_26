module barrel_shifter_sva (
    input logic clk,
    input logic [3:0] D,
    input logic [1:0] A,
    input logic [3:0] S
);

// A=00 passes D through unchanged.
    check_a00_passthrough: assert property (
        @(posedge clk) (A == 2'b00) |-> (S == D)
    );

// A=01 shifts left by 1 with zero fill.
    check_a01_shift1: assert property (
        @(posedge clk) (A == 2'b01) |-> (S == {D[2:0], 1'b0})
    );

// A=10 shifts left by 2 with zero fill.
    check_a10_shift2: assert property (
        @(posedge clk) (A == 2'b10) |-> (S == {D[1:0], 2'b00})
    );

// A=11 shifts left by 3 with zero fill.
    check_a11_shift3: assert property (
        @(posedge clk) (A == 2'b11) |-> (S == {D[0], 3'b000})
    );

endmodule
