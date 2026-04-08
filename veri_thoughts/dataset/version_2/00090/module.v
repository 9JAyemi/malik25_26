module binary_adder(
    input [3:0] A,
    input [3:0] B,
    output [3:0] S,
    output C
);

    wire [3:0] sum;
    wire [3:0] carry;

    full_adder fa0(.A(A[0]), .B(B[0]), .C_in(1'b0), .S(sum[0]), .C_out(carry[1]));
    full_adder fa1(.A(A[1]), .B(B[1]), .C_in(carry[1]), .S(sum[1]), .C_out(carry[2]));
    full_adder fa2(.A(A[2]), .B(B[2]), .C_in(carry[2]), .S(sum[2]), .C_out(carry[3]));
    full_adder fa3(.A(A[3]), .B(B[3]), .C_in(carry[3]), .S(sum[3]), .C_out(C));

    assign S = sum;

endmodule

module full_adder(
    input A,
    input B,
    input C_in,
    output S,
    output C_out
);

    assign {C_out, S} = A + B + C_in;

endmodule