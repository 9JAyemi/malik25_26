module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    input CIN,
    output [3:0] S,
    output COUT
);

    wire [3:0] sum;
    wire [3:0] carry;

    // Full adder for bit 0
    full_adder fa0 (sum[0], carry[0], A[0], B[0], CIN);

    // Full adder for bit 1
    full_adder fa1 (sum[1], carry[1], A[1], B[1], carry[0]);

    // Full adder for bit 2
    full_adder fa2 (sum[2], carry[2], A[2], B[2], carry[1]);

    // Full adder for bit 3
    full_adder fa3 (sum[3], carry[3], A[3], B[3], carry[2]);

    // Output
    assign S = sum;
    assign COUT = carry[3];

endmodule

module full_adder (
    output sum,
    output carry,
    input a,
    input b,
    input cin
);

    assign sum = a ^ b ^ cin;
    assign carry = (a & b) | (a & cin) | (b & cin);

endmodule