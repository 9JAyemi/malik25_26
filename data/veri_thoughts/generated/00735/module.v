
module full_adder (
    input A,
    input B,
    input C_IN,
    output wire S,
    output wire C_OUT
);

assign S = A ^ B ^ C_IN;
assign C_OUT = (A & B) | (B & C_IN) | (A & C_IN);

endmodule

module adder4bit (
    input [3:0] A,
    input [3:0] B,
    input C_IN,
    output [3:0] SUM,
    output wire C_OUT
);

wire [3:0] carry;

full_adder fa1(
    .A(A[0]),
    .B(B[0]),
    .C_IN(C_IN),
    .S(SUM[0]),
    .C_OUT(carry[0])
);

full_adder fa2(
    .A(A[1]),
    .B(B[1]),
    .C_IN(carry[0]),
    .S(SUM[1]),
    .C_OUT(carry[1])
);

full_adder fa3(
    .A(A[2]),
    .B(B[2]),
    .C_IN(carry[1]),
    .S(SUM[2]),
    .C_OUT(carry[2])
);

full_adder fa4(
    .A(A[3]),
    .B(B[3]),
    .C_IN(carry[2]),
    .S(SUM[3]),
    .C_OUT(C_OUT)
);

endmodule
