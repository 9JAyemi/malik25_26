
module full_adder (
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

    wire w1, w2, w3;

    assign w1 = a ^ b;
    assign sum = w1 ^ cin;
    assign w2 = a & b;
    assign w3 = w1 & cin;
    assign cout = w2 | w3;

endmodule

module ripple_carry_adder (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] Sum,
    output Cout
);

    wire [3:0] carry;
    full_adder fa0(A[0], B[0], Cin, Sum[0], carry[0]);
    full_adder fa1(A[1], B[1], carry[0], Sum[1], carry[1]);
    full_adder fa2(A[2], B[2], carry[1], Sum[2], carry[2]);
    full_adder fa3(A[3], B[3], carry[2], Sum[3], Cout);

endmodule
