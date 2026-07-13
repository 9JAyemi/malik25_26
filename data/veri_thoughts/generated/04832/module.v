module half_adder(
    input a,
    input b,
    output sum,
    output carry
);

    assign sum = a ^ b;
    assign carry = a & b;

endmodule

module full_adder(
    input A,
    input B,
    input Cin,
    output S,
    output Cout
);

    wire sum1, carry1, sum2, carry2;

    half_adder ha1(.a(A), .b(B), .sum(sum1), .carry(carry1));
    half_adder ha2(.a(sum1), .b(Cin), .sum(sum2), .carry(carry2));

    assign S = sum2;
    assign Cout = carry1 | carry2;

endmodule