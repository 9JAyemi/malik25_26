module ripple_carry_adder(
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] Sum,
    output Cout
);

wire [3:0] C;

// calculate sum bits
assign Sum[0] = A[0] ^ B[0] ^ Cin;
assign Sum[1] = A[1] ^ B[1] ^ C[0];
assign Sum[2] = A[2] ^ B[2] ^ C[1];
assign Sum[3] = A[3] ^ B[3] ^ C[2];

// calculate carry-out bit
assign Cout = (A[3] & B[3]) | (A[3] & C[2]) | (B[3] & C[2]);

// calculate carry bits
assign C[0] = (A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin);
assign C[1] = (A[1] & B[1]) | (A[1] & C[0]) | (B[1] & C[0]);
assign C[2] = (A[2] & B[2]) | (A[2] & C[1]) | (B[2] & C[1]);

endmodule