
module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

    wire [3:0] carry;
    full_adder fa0 (.a(A[0]), .b(B[0]), .c(Cin), .s(S[0]), .cout(carry[0]));
    full_adder fa1 (.a(A[1]), .b(B[1]), .c(carry[0]), .s(S[1]), .cout(carry[1]));
    full_adder fa2 (.a(A[2]), .b(B[2]), .c(carry[1]), .s(S[2]), .cout(carry[2]));
    full_adder fa3 (.a(A[3]), .b(B[3]), .c(carry[2]), .s(S[3]), .cout(Cout));

endmodule
module full_adder (
    input a,
    input b,
    input c,
    output s,
    output cout
);

    assign s = a ^ b ^ c;
    assign cout = (a & b) | (b & c) | (a & c);

endmodule