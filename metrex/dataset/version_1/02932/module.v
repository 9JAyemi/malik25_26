module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    output [3:0] S,
    output Cout
);

    wire [3:0] c;
    full_adder fa0 (.a(A[0]), .b(B[0]), .cin(1'b0), .sum(S[0]), .cout(c[0]));
    full_adder fa1 (.a(A[1]), .b(B[1]), .cin(c[0]), .sum(S[1]), .cout(c[1]));
    full_adder fa2 (.a(A[2]), .b(B[2]), .cin(c[1]), .sum(S[2]), .cout(c[2]));
    full_adder fa3 (.a(A[3]), .b(B[3]), .cin(c[2]), .sum(S[3]), .cout(Cout));

endmodule

module full_adder (
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

    assign sum = a ^ b ^ cin;
    assign cout = (a & b) | (a & cin) | (b & cin);

endmodule