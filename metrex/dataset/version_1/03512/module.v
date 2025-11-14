
module half_adder(
    input A,
    input B,
    output S,
    output C
);

assign {C, S} = A + B;

endmodule
module full_adder(
    input A,
    input B,
    input Cin,
    output S,
    output Cout
);

assign {Cout, S} = A + B + Cin;

endmodule
module adder_4bit(
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

wire [3:0] C;
wire [2:0] S1;

half_adder HA0(A[0], B[0], S[0], C[0]);
full_adder FA1(A[1], B[1], C[0], S1[0], C[1]);
full_adder FA2(A[2], B[2], C[1], S1[1], C[2]);
full_adder FA3(A[3], B[3], C[2], S[3], Cout);

assign S = {S[3], S1, S[0]};

endmodule