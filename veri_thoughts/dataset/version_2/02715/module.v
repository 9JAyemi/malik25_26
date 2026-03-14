module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    input CI,
    output CO,
    output [3:0] S
);

wire [3:0] C; // intermediate carry values
wire [3:0] X; // intermediate sum values

// full adder for bit 0
full_adder FA0(A[0], B[0], CI, C[0], X[0]);

// full adder for bit 1
full_adder FA1(A[1], B[1], C[0], C[1], X[1]);

// full adder for bit 2
full_adder FA2(A[2], B[2], C[1], C[2], X[2]);

// full adder for bit 3
full_adder FA3(A[3], B[3], C[2], CO, X[3]);

assign S = X;

endmodule

module full_adder(
    input A,
    input B,
    input CI,
    output CO,
    output S
);

assign {CO, S} = A + B + CI;

endmodule