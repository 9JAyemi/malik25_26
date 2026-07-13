
module binary_adder(input [3:0] A, B, output [3:0] S, output C_out);
    wire [3:0] sum;
    wire [4:1] carry; // 4:1 to include C_in

    // Full adder for bit 0
    full_adder fa0(A[0], B[0], 1'b0, sum[0], carry[1]);

    // Full adder for bit 1
    full_adder fa1(A[1], B[1], carry[1], sum[1], carry[2]);

    // Full adder for bit 2
    full_adder fa2(A[2], B[2], carry[2], sum[2], carry[3]);

    // Full adder for bit 3
    full_adder fa3(A[3], B[3], carry[3], sum[3], C_out);

    assign S = sum;
endmodule
module full_adder(input a, b, c_in, output s, output c_out);
    wire w1, w2, w3;

    xor(w1, a, b);
    xor(s, w1, c_in);
    and(w2, a, b);
    and(w3, w1, c_in);
    or(c_out, w2, w3);
endmodule