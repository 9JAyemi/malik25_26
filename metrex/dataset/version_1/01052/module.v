module full_adder (
    input A,
    input B,
    input Cin,
    output S,
    output Cout
);
    // Implementing full adder using structural verilog
    wire w1, w2, w3;
    xor x1(w1, A, B);
    xor x2(S, w1, Cin);
    and a1(w2, A, B);
    and a2(w3, w1, Cin);
    or o1(Cout, w2, w3);
endmodule

module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);
    wire c0, c1, c2;
    full_adder fa0(A[0], B[0], Cin, S[0], c0);
    full_adder fa1(A[1], B[1], c0, S[1], c1);
    full_adder fa2(A[2], B[2], c1, S[2], c2);
    full_adder fa3(A[3], B[3], c2, S[3], Cout);
endmodule