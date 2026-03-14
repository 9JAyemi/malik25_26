module full_adder (
    input A,
    input B,
    input C_in,
    output S,
    output C_out
);

    assign S = A ^ B ^ C_in;
    assign C_out = (A & B) | (C_in & (A ^ B));

endmodule

module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    input C_in,
    output [3:0] S,
    output C_out
);

    wire c1, c2, c3;

    full_adder fa0(.A(A[0]), .B(B[0]), .C_in(C_in), .S(S[0]), .C_out(c1));
    full_adder fa1(.A(A[1]), .B(B[1]), .C_in(c1), .S(S[1]), .C_out(c2));
    full_adder fa2(.A(A[2]), .B(B[2]), .C_in(c2), .S(S[2]), .C_out(c3));
    full_adder fa3(.A(A[3]), .B(B[3]), .C_in(c3), .S(S[3]), .C_out(C_out));

endmodule