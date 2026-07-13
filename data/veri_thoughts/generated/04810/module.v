
module adder_4bit(
    input [3:0] in1,
    input [3:0] in2,
    input cin,
    output [3:0] out,
    output cout
);

    wire [3:0] sum;
    wire c1, c2, c3;

    // Full-adder for bit 0
    full_adder fa0(.a(in1[0]), .b(in2[0]), .cin(cin), .sum(sum[0]), .cout(c1));

    // Full-adder for bit 1
    full_adder fa1(.a(in1[1]), .b(in2[1]), .cin(c1), .sum(sum[1]), .cout(c2));

    // Full-adder for bit 2
    full_adder fa2(.a(in1[2]), .b(in2[2]), .cin(c2), .sum(sum[2]), .cout(c3));

    // Full-adder for bit 3
    full_adder fa3(.a(in1[3]), .b(in2[3]), .cin(c3), .sum(sum[3]), .cout(cout));

    assign out = sum;

endmodule
module full_adder(
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

    wire s1, s2, s3;

    // XOR gates for sum
    xor (s1, a, b);
    xor (sum, s1, cin);

    // AND gates for carry-out
    and (s2, a, b);
    and (s3, s1, cin);
    or (cout, s2, s3);

endmodule