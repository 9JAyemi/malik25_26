
module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    input C_in,
    output [3:0] Sum,
    output C_out
);

    wire [3:0] carry;
    wire [3:0] sum;

    assign carry[0] = C_in;

    // Instantiate full adders
    full_adder fa1(.a(A[0]), .b(B[0]), .cin(carry[0]), .sum(sum[0]), .cout(carry[1]));
    full_adder fa2(.a(A[1]), .b(B[1]), .cin(carry[1]), .sum(sum[1]), .cout(carry[2]));
    full_adder fa3(.a(A[2]), .b(B[2]), .cin(carry[2]), .sum(sum[2]), .cout(carry[3]));
    full_adder fa4(.a(A[3]), .b(B[3]), .cin(carry[3]), .sum(sum[3]), .cout(C_out));

    assign Sum = sum;

endmodule

module full_adder(
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

    assign sum = a ^ b ^ cin;
    assign cout = (a & b) | (b & cin) | (cin & a);

endmodule
