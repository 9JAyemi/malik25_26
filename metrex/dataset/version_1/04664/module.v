module binary_adder(
    input [4:0] a,
    input [4:0] b,
    output [4:0] sum,
    output carry
);

    wire c1, c2, c3, c4, c5;
    wire s1, s2, s3, s4, s5;

    // Full Adders
    full_adder fa1(a[0], b[0], 1'b0, s1, c1);
    full_adder fa2(a[1], b[1], c1, s2, c2);
    full_adder fa3(a[2], b[2], c2, s3, c3);
    full_adder fa4(a[3], b[3], c3, s4, c4);
    full_adder fa5(a[4], b[4], c4, s5, c5);

    // Sum output
    assign sum = {s5, s4, s3, s2, s1};
    
    // Carry output
    assign carry = c5;

endmodule

module full_adder(
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

    wire s1, c1, c2;

    // Half Adder 1
    half_adder ha1(a, b, s1, c1);
    
    // Half Adder 2
    half_adder ha2(s1, cin, sum, c2);
    
    // Carry output
    assign cout = c1 | c2;

endmodule

module half_adder(
    input a,
    input b,
    output sum,
    output carry
);

    // Sum output
    assign sum = a ^ b;
    
    // Carry output
    assign carry = a & b;

endmodule