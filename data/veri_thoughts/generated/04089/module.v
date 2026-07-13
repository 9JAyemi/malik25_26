module binary_adder(
    input [3:0] A,
    input [3:0] B,
    input CIN,
    output [3:0] SUM,
    output COUT
);

    wire [3:0] carry;
    wire [3:0] sum;

    full_adder fa0(A[0], B[0], CIN, sum[0], carry[0]);
    full_adder fa1(A[1], B[1], carry[0], sum[1], carry[1]);
    full_adder fa2(A[2], B[2], carry[1], sum[2], carry[2]);
    full_adder fa3(A[3], B[3], carry[2], sum[3], COUT);

    assign SUM = sum;

endmodule

module full_adder(
    input A,
    input B,
    input CIN,
    output SUM,
    output COUT
);

    assign SUM = A ^ B ^ CIN;
    assign COUT = (A & B) | (A & CIN) | (B & CIN);

endmodule