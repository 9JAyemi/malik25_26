module ripple_carry_adder(
    input [3:0] A,
    input [3:0] B,
    input CI,
    output [3:0] S,
    output CO
);

    wire [4:0] C;
    full_adder fa0(.CO(C[0]), .S(S[0]), .A(A[0]), .B(B[0]), .CI(CI));
    full_adder fa1(.CO(C[1]), .S(S[1]), .A(A[1]), .B(B[1]), .CI(C[0]));
    full_adder fa2(.CO(C[2]), .S(S[2]), .A(A[2]), .B(B[2]), .CI(C[1]));
    full_adder fa3(.CO(CO), .S(S[3]), .A(A[3]), .B(B[3]), .CI(C[2]));

endmodule

module full_adder (
    input A,
    input B,
    input CI,
    output S,
    output CO
);

    assign {CO, S} = A + B + CI;

endmodule