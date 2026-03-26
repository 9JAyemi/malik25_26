module adder_4bit(
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

wire [3:0] sum;
wire [3:0] carry;

full_adder fa0(A[0], B[0], Cin, sum[0], carry[0]);
full_adder fa1(A[1], B[1], carry[0], sum[1], carry[1]);
full_adder fa2(A[2], B[2], carry[1], sum[2], carry[2]);
full_adder fa3(A[3], B[3], carry[2], sum[3], Cout);

assign S = sum;

endmodule

module full_adder(
    input A,
    input B,
    input Cin,
    output S,
    output Cout
);

wire s1, c1, c2;

xor (s1, A, B);
xor (S, s1, Cin);
and (c1, A, B);
and (c2, s1, Cin);
or (Cout, c1, c2);

endmodule