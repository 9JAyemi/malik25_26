module adder_4bit_carry (
    // Inputs
    input [3:0] a,
    input [3:0] b,
    input cin,
    // Outputs
    output [3:0] sum,
    output cout
);

    wire [3:0] temp_sum;
    wire c1, c2, c3;

    // First bit
    full_adder fa1(a[0], b[0], cin, temp_sum[0], c1);

    // Second bit
    full_adder fa2(a[1], b[1], c1, temp_sum[1], c2);

    // Third bit
    full_adder fa3(a[2], b[2], c2, temp_sum[2], c3);

    // Fourth bit
    full_adder fa4(a[3], b[3], c3, temp_sum[3], cout);

    assign sum = temp_sum;

endmodule

module full_adder (
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

    wire s1, s2, s3;

    // First XOR gate
    xor x1(s1, a, b);

    // Second XOR gate
    xor x2(s2, s1, cin);

    // Third AND gate
    and a1(s3, s1, cin);

    // Final sum output
    assign sum = s2;

    // Final carry output
    assign cout = s3;

endmodule