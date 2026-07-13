module full_adder (
    input A,
    input B,
    input Cin,
    output S,
    output Cout
);

    assign {Cout, S} = A + B + Cin;

endmodule

module ripple_carry_adder (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

    wire [3:0] S_i;
    wire [3:0] Cout_i;

    full_adder fa0 (.A(A[0]), .B(B[0]), .Cin(Cin), .S(S_i[0]), .Cout(Cout_i[0]));
    full_adder fa1 (.A(A[1]), .B(B[1]), .Cin(Cout_i[0]), .S(S_i[1]), .Cout(Cout_i[1]));
    full_adder fa2 (.A(A[2]), .B(B[2]), .Cin(Cout_i[1]), .S(S_i[2]), .Cout(Cout_i[2]));
    full_adder fa3 (.A(A[3]), .B(B[3]), .Cin(Cout_i[2]), .S(S_i[3]), .Cout(Cout));

    assign S = S_i;

endmodule