
module full_adder (
    input A,
    input B,
    input CI,
    output COUT,
    output SUM
);

wire temp_sum;

one_bit_adder u_o1(.A(A), .B(B), .CI(CI), .COUT(COUT), .SUM(temp_sum));
assign SUM = temp_sum ^ CI;

endmodule
module one_bit_adder (
    input A,
    input B,
    input CI,
    output COUT,
    output SUM
);
    assign SUM = (A ^ B) ^ CI;
    assign COUT = (A & B) | (A & CI) | (B & CI);
endmodule
module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    input CI,
    output [3:0] SUM,
    output COUT
);

wire C1, C2, C3;
full_adder u_f1(.A(A[0]), .B(B[0]), .CI(CI), .COUT(C1), .SUM(SUM[0]));
full_adder u_f2(.A(A[1]), .B(B[1]), .CI(C1), .COUT(C2), .SUM(SUM[1]));
full_adder u_f3(.A(A[2]), .B(B[2]), .CI(C2), .COUT(C3), .SUM(SUM[2]));
full_adder u_f4(.A(A[3]), .B(B[3]), .CI(C3), .COUT(COUT), .SUM(SUM[3]));

endmodule