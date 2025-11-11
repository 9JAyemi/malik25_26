
module add_sub (
    input [3:0] A,
    input [3:0] B,
    input S,   // 0: addition, 1: subtraction
    output [3:0] R,
    output Cout
);

    wire [3:0] sum;
    wire [4:0] C;  // 4-bit wire for carry

    assign Cout = S ? (~A[0] & B[0]) : (A[0] & B[0]);
    assign C[0] = S ? (A[0] & B[0]) : (~A[0] & B[0]);

    full_adder FA0(A[0], B[0], C[0], R[0], C[1]);
    full_adder FA1(A[1], B[1], C[1], R[1], C[2]);
    full_adder FA2(A[2], B[2], C[2], R[2], C[3]);
    full_adder FA3(A[3], B[3], C[3], R[3], C[4]);

endmodule
module full_adder (
    input A,
    input B,
    input Cin,
    output S,
    output Cout
);

    assign S = A ^ B ^ Cin;
    assign Cout = (A & B) | (Cin & (A ^ B));

endmodule