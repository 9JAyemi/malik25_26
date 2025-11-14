
module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] Sum,
    output Cout
);

    wire [3:0] temp_sum;
    wire [3:0] temp_carry;

    // Full adder for least significant bit
    full_adder FA0(A[0], B[0], Cin, temp_sum[0], temp_carry[0]);

    // Full adder for second least significant bit
    full_adder FA1(A[1], B[1], temp_carry[0], temp_sum[1], temp_carry[1]);

    // Full adder for third least significant bit
    full_adder FA2(A[2], B[2], temp_carry[1], temp_sum[2], temp_carry[2]);

    // Full adder for most significant bit
    full_adder FA3(A[3], B[3], temp_carry[2], temp_sum[3], Cout);

    assign Sum = temp_sum;

endmodule
module full_adder (
    input A,
    input B,
    input Cin,
    output Sum,
    output Cout
);

    assign Sum = A ^ B ^ Cin;
    assign Cout = (A & B) | (Cin & (A ^ B));

endmodule