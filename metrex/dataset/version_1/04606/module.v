module full_adder(
    input A,
    input B,
    input CI,
    output S,
    output CO
);

assign S = A ^ B ^ CI;
assign CO = (A & B) | (CI & (A ^ B));

endmodule

module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    output [4:0] C,
    output CO
);

wire [3:0] S;
wire [3:0] CO_int;

full_adder FA0(.A(A[0]), .B(B[0]), .CI(1'b0), .S(S[0]), .CO(CO_int[0]));
full_adder FA1(.A(A[1]), .B(B[1]), .CI(CO_int[0]), .S(S[1]), .CO(CO_int[1]));
full_adder FA2(.A(A[2]), .B(B[2]), .CI(CO_int[1]), .S(S[2]), .CO(CO_int[2]));
full_adder FA3(.A(A[3]), .B(B[3]), .CI(CO_int[2]), .S(S[3]), .CO(CO));

assign C = {CO, S};

endmodule