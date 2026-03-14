module ripple_carry_adder (
    input [3:0] A,
    input [3:0] B,
    output [3:0] OUT
);

    wire [3:0] carry;
    wire [3:0] sum;

    full_adder fa0(A[0], B[0], 1'b0, sum[0], carry[0]);
    full_adder fa1(A[1], B[1], carry[0], sum[1], carry[1]);
    full_adder fa2(A[2], B[2], carry[1], sum[2], carry[2]);
    full_adder fa3(A[3], B[3], carry[2], sum[3], carry[3]);

    assign OUT = sum;

endmodule

module full_adder (
    input A,
    input B,
    input CIN,
    output SUM,
    output COUT
);

    assign {COUT, SUM} = A + B + CIN;

endmodule