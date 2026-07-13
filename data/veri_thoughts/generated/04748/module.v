module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] Sum,
    output Cout
);

    wire [3:0] temp_sum;
    wire [3:0] temp_carry;

    // Full Adder
    assign temp_sum[0] = A[0] ^ B[0] ^ Cin;
    assign temp_carry[0] = (A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin);

    assign temp_sum[1] = A[1] ^ B[1] ^ temp_carry[0];
    assign temp_carry[1] = (A[1] & B[1]) | (A[1] & temp_carry[0]) | (B[1] & temp_carry[0]);

    assign temp_sum[2] = A[2] ^ B[2] ^ temp_carry[1];
    assign temp_carry[2] = (A[2] & B[2]) | (A[2] & temp_carry[1]) | (B[2] & temp_carry[1]);

    assign temp_sum[3] = A[3] ^ B[3] ^ temp_carry[2];
    assign Cout = (A[3] & B[3]) | (A[3] & temp_carry[2]) | (B[3] & temp_carry[2]);

    assign Sum = temp_sum;

endmodule