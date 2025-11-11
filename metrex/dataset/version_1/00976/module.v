module two_bit_adder (
    input [1:0] A,
    input [1:0] B,
    input Cin,
    output [1:0] Sum,
    output Cout
);

    wire c1, c2, s1, s2;

    // Full adder for bit 0
    full_adder fa0 (
        .a(A[0]),
        .b(B[0]),
        .cin(Cin),
        .sum(s1),
        .cout(c1)
    );

    // Full adder for bit 1
    full_adder fa1 (
        .a(A[1]),
        .b(B[1]),
        .cin(c1),
        .sum(s2),
        .cout(c2)
    );

    // Output signals
    assign Sum[0] = s1;
    assign Sum[1] = s2;
    assign Cout = c2;

endmodule

module full_adder (
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

    wire c1, c2, s1;

    // First half adder
    half_adder ha1 (
        .a(a),
        .b(b),
        .sum(s1),
        .carry(c1)
    );

    // Second half adder
    half_adder ha2 (
        .a(s1),
        .b(cin),
        .sum(sum),
        .carry(c2)
    );

    // Carry out
    assign cout = c1 | c2;

endmodule

module half_adder (
    input a,
    input b,
    output sum,
    output carry
);

    assign sum = a ^ b;
    assign carry = a & b;

endmodule