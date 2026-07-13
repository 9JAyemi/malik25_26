
module four_bit_adder (
    input  wire [3:0] A,
    input  wire [3:0] B,
    output wire [3:0] S,
    output wire       Cout
);

    wire [3:0] C;

    full_adder fa0 (.a(A[0]), .b(B[0]), .c_in(1'b0), .s(S[0]), .c_out(C[0]));
    full_adder fa1 (.a(A[1]), .b(B[1]), .c_in(C[0]), .s(S[1]), .c_out(C[1]));
    full_adder fa2 (.a(A[2]), .b(B[2]), .c_in(C[1]), .s(S[2]), .c_out(C[2]));
    full_adder fa3 (.a(A[3]), .b(B[3]), .c_in(C[2]), .s(S[3]), .c_out(Cout));

endmodule

module full_adder (
    input  wire a,
    input  wire b,
    input  wire c_in,
    output wire s,
    output wire c_out
);

    assign s = a ^ b ^ c_in;
    assign c_out = (a & b) | (a & c_in) | (b & c_in);

endmodule
