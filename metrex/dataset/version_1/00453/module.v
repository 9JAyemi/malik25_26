module full_adder (
    input a, b, cin,
    output cout, sum
);

    assign sum = a ^ b ^ cin;
    assign cout = (a & b) | (a & cin) | (b & cin);

endmodule

module bit_reversal (
    input [7:0] in,
    output [7:0] out
);

    assign out = {in[7], in[6], in[5], in[4], in[3], in[2], in[1], in[0]};

endmodule

module final_module (
    input [7:0] in,
    input a, b, cin,
    output cout, sum,
    output [7:0] out
);

    wire [7:0] reversed_in;
    bit_reversal br(
        .in(in),
        .out(reversed_in)
    );

    wire cout_fa;
    wire sum_fa;
    full_adder fa(
        .a(a),
        .b(b),
        .cin(cin),
        .sum(sum_fa),
        .cout(cout_fa)
    );

    assign sum = sum_fa;
    assign cout = cout_fa;

    assign out = sum | reversed_in;

endmodule

module top_module (
    input [7:0] in,
    input a, b, cin,
    output cout, sum,
    output [7:0] out
);

    final_module fm(
        .in(in),
        .a(a),
        .b(b),
        .cin(cin),
        .sum(sum),
        .cout(cout),
        .out(out)
    );

endmodule