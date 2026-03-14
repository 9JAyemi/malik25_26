
module ripple_carry_adder (
    A    ,
    B    ,
    C_in ,
    CLK  ,
    S    ,
    C_out
);

    input  [3:0] A;
    input  [3:0] B;
    input  C_in;
    input  CLK;
    output [3:0] S;
    output C_out;

    wire [3:0] sum;
    wire [3:0] carry; // 4 bits carry

    // Full adder module
    full_adder fa0(sum[0], carry[0], A[0], B[0], C_in);
    full_adder fa1(sum[1], carry[1], A[1], B[1], carry[0]);
    full_adder fa2(sum[2], carry[2], A[2], B[2], carry[1]);
    full_adder fa3(sum[3], C_out, A[3], B[3], carry[2]);

    // Connect the sum outputs of the full adders to the S output of the ripple carry adder module
    assign S = sum;

endmodule
module full_adder (
    sum  ,
    carry,
    A    ,
    B    ,
    C_in
);

    output sum;
    output carry;
    input  A;
    input  B;
    input  C_in;

    assign sum   = A ^ B ^ C_in;
    assign carry = (A & B) | (A & C_in) | (B & C_in);

endmodule