module adder4 (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

    wire [3:0] sum;
    wire [3:1] carry;

    // Full adder for bit 0
    full_adder FA0(A[0], B[0], Cin, sum[0], carry[1]);

    // Full adder for bit 1
    full_adder FA1(A[1], B[1], carry[1], sum[1], carry[2]);

    // Full adder for bit 2
    full_adder FA2(A[2], B[2], carry[2], sum[2], carry[3]);

    // Full adder for bit 3
    full_adder FA3(A[3], B[3], carry[3], sum[3], Cout);

    assign S = sum;

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