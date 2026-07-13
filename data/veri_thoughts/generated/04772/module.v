module full_adder(
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

    assign sum = a ^ b ^ cin;
    assign cout = (a & b) | (a & cin) | (b & cin);

endmodule

module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    output [3:0] S,
    output C_out
);

    wire [3:0] carry;

    full_adder FA0(A[0], B[0], 1'b0, S[0], carry[0]);
    full_adder FA1(A[1], B[1], carry[0], S[1], carry[1]);
    full_adder FA2(A[2], B[2], carry[1], S[2], carry[2]);
    full_adder FA3(A[3], B[3], carry[2], S[3], C_out);

endmodule