module adder_4bit(
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

wire [3:0] C; // intermediate carry bits

// full-adder for each bit
full_adder FA0(.A(A[0]), .B(B[0]), .Cin(Cin), .S(S[0]), .C(C[0]));
full_adder FA1(.A(A[1]), .B(B[1]), .Cin(C[0]), .S(S[1]), .C(C[1]));
full_adder FA2(.A(A[2]), .B(B[2]), .Cin(C[1]), .S(S[2]), .C(C[2]));
full_adder FA3(.A(A[3]), .B(B[3]), .Cin(C[2]), .S(S[3]), .C(Cout));

endmodule

// full-adder module
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