module ripple_carry_adder(
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

wire [3:0] C;

// Full adder for the least significant bit
full_adder FA0(
    .A(A[0]),
    .B(B[0]),
    .Cin(Cin),
    .S(S[0]),
    .C(C[0])
);

// Full adder for the second least significant bit
full_adder FA1(
    .A(A[1]),
    .B(B[1]),
    .Cin(C[0]),
    .S(S[1]),
    .C(C[1])
);

// Full adder for the second most significant bit
full_adder FA2(
    .A(A[2]),
    .B(B[2]),
    .Cin(C[1]),
    .S(S[2]),
    .C(C[2])
);

// Full adder for the most significant bit
full_adder FA3(
    .A(A[3]),
    .B(B[3]),
    .Cin(C[2]),
    .S(S[3]),
    .C(Cout)
);

endmodule


module full_adder(
    input A,
    input B,
    input Cin,
    output S,
    output C
);

assign S = A ^ B ^ Cin;
assign C = (A & B) | (A & Cin) | (B & Cin);

endmodule