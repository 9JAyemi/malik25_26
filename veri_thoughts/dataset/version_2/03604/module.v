module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

    wire [3:0] sum;
    wire c1, c2, c3;

    full_adder fa0 (.a(A[0]), .b(B[0]), .cin(Cin), .sum(sum[0]), .cout(c1));
    full_adder fa1 (.a(A[1]), .b(B[1]), .cin(c1), .sum(sum[1]), .cout(c2));
    full_adder fa2 (.a(A[2]), .b(B[2]), .cin(c2), .sum(sum[2]), .cout(c3));
    full_adder fa3 (.a(A[3]), .b(B[3]), .cin(c3), .sum(sum[3]), .cout(Cout));

    assign S = sum;

endmodule

module full_adder (
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

    assign {cout, sum} = a + b + cin;

endmodule