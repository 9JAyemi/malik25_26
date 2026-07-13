module r4_adder(output [3:0] S, output Cout, input [3:0] A, B, input Cin);

    wire c1, c2, c3;

    full_adder a1(.S(S[0]), .Cout(c1), .A(A[0]), .B(B[0]), .Cin(Cin)),
               a2(.S(S[1]), .Cout(c2), .A(A[1]), .B(B[1]), .Cin(c1)),
               a3(.S(S[2]), .Cout(c3), .A(A[2]), .B(B[2]), .Cin(c2)),
               a4(.S(S[3]), .Cout(Cout), .A(A[3]), .B(B[3]), .Cin(c3));

endmodule

module full_adder(output S, output Cout, input A, B, input Cin);
    assign {Cout, S} = A + B + Cin;
endmodule