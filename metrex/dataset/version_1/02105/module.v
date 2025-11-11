
module full_adder_2bit(
    input [1:0] A,
    input [1:0] B,
    input Cin,
    output [1:0] Sum,
    output Cout
);

wire [1:0] s1, s2, s3;
wire c1, c2, c3;

// First adder
nand (s1[0], A[0], B[0], Cin);
nand (c1, A[0], B[0]);

// Second adder
nand (s2[0], A[1], B[1], s1[0]);
nand (c2, A[1], B[1]);

// Third adder
nand (s3[0], A[0], B[0], B[1]);
nand (c3, A[0], B[0]);

assign Sum = {s2[0], s3[0]};
assign Cout = (Cin & c1) | (c2 & s1[0]) | (c3 & s2[0]);

endmodule
