
module reverse_byte_order(
    input [31:0] in,
    output [31:0] out
);

    assign out = {in[7:0], in[15:8], in[23:16], in[31:24]};

endmodule
module full_adder(
    input a,
    input b,
    input cin,
    output reg sum,
    output reg cout
);

    always @ (a or b or cin) begin
        {cout, sum} = a + b + cin;
    end

endmodule
module adder_with_carry_in(
    input [3:0] a,
    input [3:0] b,
    input cin,
    output [4:0] sum
);

    wire c1, c2, c3;

    full_adder fa1(.a(a[0]), .b(b[0]), .cin(cin), .sum(sum[0]), .cout(c1));
    full_adder fa2(.a(a[1]), .b(b[1]), .cin(c1), .sum(sum[1]), .cout(c2));
    full_adder fa3(.a(a[2]), .b(b[2]), .cin(c2), .sum(sum[2]), .cout(c3));
    full_adder fa4(.a(a[3]), .b(b[3]), .cin(c3), .sum(sum[3]), .cout(sum[4]));

endmodule
module top_module(
    input [31:0] in1,
    input [31:0] in2,
    input cin,
    output [31:0] out
);

    wire [31:0] rev_in1, rev_in2;
    wire [4:0] sum;

    reverse_byte_order rbo1(.in(in1), .out(rev_in1));
    reverse_byte_order rbo2(.in(in2), .out(rev_in2));
    adder_with_carry_in awci(.a(rev_in1[3:0]), .b(rev_in2[3:0]), .cin(cin), .sum(sum));
    reverse_byte_order rbo3(.in({sum[4], sum[3:0], 27'b0}), .out(out));

endmodule