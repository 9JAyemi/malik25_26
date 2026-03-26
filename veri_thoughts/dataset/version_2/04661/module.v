
module full_adder_4bit(
    input [3:0] A,
    input [3:0] B,
    input CIN,
    output [3:0] SUM,
    output COUT
);

    wire [3:0] sum, carry;

    assign carry[0] = CIN;
    assign {carry[1], sum[0]} = A[0] + B[0] + carry[0];
    assign {carry[2], sum[1]} = A[1] + B[1] + carry[1];
    assign {carry[3], sum[2]} = A[2] + B[2] + carry[2];
    assign {COUT, sum[3]} = A[3] + B[3] + carry[3];

    assign SUM = sum;

endmodule