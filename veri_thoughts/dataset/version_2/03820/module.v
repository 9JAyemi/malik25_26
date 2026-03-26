module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    output [3:0] S,
    output Cout
);

    wire [3:0] carry;
    wire [3:0] sum;

    full_adder FA0(A[0], B[0], 1'b0, sum[0], carry[0]);
    full_adder FA1(A[1], B[1], carry[0], sum[1], carry[1]);
    full_adder FA2(A[2], B[2], carry[1], sum[2], carry[2]);
    full_adder FA3(A[3], B[3], carry[2], sum[3], Cout);

    assign S = sum;

endmodule

module full_adder(
    input A,
    input B,
    input Cin,
    output S,
    output Cout
);

    wire sum;
    wire carry;

    assign sum = A ^ B;
    assign carry = A & B;

    assign S = sum ^ Cin;
    assign Cout = carry | (sum & Cin);

endmodule