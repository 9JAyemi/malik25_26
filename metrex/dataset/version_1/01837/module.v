module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] Sum,
    output Cout
);

    wire [3:0] S;
    wire C1, C2, C3;

    // Instantiate full adders
    full_adder FA0 (.A(A[0]), .B(B[0]), .Cin(Cin), .S(S[0]), .Cout(C1));
    full_adder FA1 (.A(A[1]), .B(B[1]), .Cin(C1), .S(S[1]), .Cout(C2));
    full_adder FA2 (.A(A[2]), .B(B[2]), .Cin(C2), .S(S[2]), .Cout(C3));
    full_adder FA3 (.A(A[3]), .B(B[3]), .Cin(C3), .S(S[3]), .Cout(Cout));

    // Assign outputs
    assign Sum = S;

endmodule

module full_adder (
    input A,
    input B,
    input Cin,
    output S,
    output Cout
);

    wire S1, C1, C2;

    // XOR gate
    xor (S1, A, B);

    // AND gates
    and (C1, A, B);
    and (C2, S1, Cin);

    // OR gate
    or (Cout, C1, C2);

    // Assign outputs
    assign S = S1;

endmodule