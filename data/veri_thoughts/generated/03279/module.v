
module adder4bit (A, B, Cin, Sum, Cout);
input [3:0] A, B;
input Cin;
output [3:0] Sum;
output Cout;

wire [3:0] C;

full_adder fa0(A[0], B[0], Cin, Sum[0], C[0]);
full_adder fa1(A[1], B[1], C[0], Sum[1], C[1]);
full_adder fa2(A[2], B[2], C[1], Sum[2], C[2]);
full_adder fa3(A[3], B[3], C[2], Sum[3], Cout);

endmodule
module full_adder (A, B, Cin, Sum, Cout);
input A, B, Cin;
output Sum, Cout;

wire x1, a1, a2;

xor (x1, A, B);
xor (Sum, x1, Cin);
and (a1, x1, Cin);
and (a2, A, B);
or (Cout, a1, a2);

endmodule