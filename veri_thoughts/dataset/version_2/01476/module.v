module four_bit_adder (
	input [3:0] A,
	input [3:0] B,
	input Cin,
	output [3:0] S,
	output Cout
);

	wire [3:0] X;
	wire [3:0] Y;
	wire C1, C2, C3;

	// Define NAND gate using primitive gates
	assign X[0] = ~(A[0] & B[0]);
	assign Y[0] = ~(X[0] & Cin);
	assign C1 = ~(B[0] & Cin);

	assign X[1] = ~(A[1] & B[1]);
	assign Y[1] = ~(X[1] & C1);
	assign C2 = ~(B[1] & C1);

	assign X[2] = ~(A[2] & B[2]);
	assign Y[2] = ~(X[2] & C2);
	assign C3 = ~(B[2] & C2);

	assign X[3] = ~(A[3] & B[3]);
	assign S[3] = ~(X[3] & C3);
	assign Cout = ~(B[3] & C3);

	assign S[2] = Y[2];
	assign S[1] = Y[1];
	assign S[0] = Y[0];
endmodule