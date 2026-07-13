module FA(
    input A,
    input B,
    input C_in,
    output S,
    output C_out
);

    assign S = A ^ B ^ C_in;
    assign C_out = (A & B) | (C_in & (A ^ B));

endmodule

module adder4(
    input [3:0] A,
    input [3:0] B,
    output [3:0] S,
    output C_out
);

    wire [3:0] S_int;
    wire C1, C2, C3;

    FA fa0(.A(A[0]), .B(B[0]), .C_in(1'b0), .S(S_int[0]), .C_out(C1));
    FA fa1(.A(A[1]), .B(B[1]), .C_in(C1), .S(S_int[1]), .C_out(C2));
    FA fa2(.A(A[2]), .B(B[2]), .C_in(C2), .S(S_int[2]), .C_out(C3));
    FA fa3(.A(A[3]), .B(B[3]), .C_in(C3), .S(S_int[3]), .C_out(C_out));

    assign S = S_int;

endmodule