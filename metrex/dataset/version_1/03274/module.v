
module ripple_carry_adder(
    input [31:0] a,
    input [31:0] b,
    input cin,
    output [31:0] sum,
    output cout
);

wire [31:0] s;
wire [31:0] c;

assign s = a ^ b ^ cin;
assign c = (a & b) | (a & cin) | (b & cin);

assign sum = s;
assign cout = c[31];

endmodule
module carry_save_adder(
    input [31:0] a,
    input [31:0] b,
    input cin,
    output [31:0] sum,
    output carry
);

wire [31:0] s1;
wire c1, c2;

ripple_carry_adder rca1(.a(a), .b(b), .cin(1'b0), .sum(s1), .cout(c1));
ripple_carry_adder rca2(.a(s1), .b({31'b0, cin}), .cin(c1), .sum(sum), .cout(c2));

assign carry = c2;

endmodule
module top_module(
    input [31:0] a,
    input [31:0] b,
    input sub,
    output [31:0] sum
);

wire [31:0] b_inverted;
wire cin;

assign b_inverted = sub ? ~b : b;
assign cin = sub ? 1'b1 : 1'b0;

carry_save_adder csa(.a(a), .b(b_inverted), .cin(cin), .sum(sum), .carry());

endmodule