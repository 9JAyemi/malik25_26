module binary_adder_shift(
    input [3:0] A,
    input [3:0] B,
    input [1:0] SHIFT,
    output [3:0] S
);

    wire [4:0] sum;
    wire [3:0] shifted_sum;

    binary_adder adder(.A(A), .B(B), .S(sum));

    barrel_shifter shifter(.IN(sum[3:0]), .SHIFT(SHIFT), .OUT(shifted_sum));

    assign S = shifted_sum;

endmodule

module binary_adder(
    input [3:0] A,
    input [3:0] B,
    output [4:0] S
);

    assign S = A + B;

endmodule

module barrel_shifter(
    input [3:0] IN,
    input [1:0] SHIFT,
    output [3:0] OUT
);

    assign OUT = (SHIFT[1]) ? {IN[1:0], 2'b00} : (SHIFT[0]) ? {IN[2:0], 1'b0} : {1'b0, IN[3:1]};

endmodule