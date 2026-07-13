module top_module (
    input clk,
    input reset,
    input [2:0] a,
    input [2:0] b,
    output [6:0] seg
);

wire [3:0] sum_full_adder, sum_half_full_adder;
wire carry_out_full_adder, carry_out_half_full_adder;

full_adder_3bit full_adder_inst (
    .a(a),
    .b(b),
    .sum(sum_full_adder),
    .carry_out(carry_out_full_adder)
);

half_full_adder_3bit half_full_adder_inst (
    .a(a),
    .b(b),
    .sum(sum_half_full_adder),
    .carry_out(carry_out_half_full_adder)
);

sum_module sum_inst (
    .sum_full_adder(sum_full_adder),
    .sum_half_full_adder(sum_half_full_adder),
    .final_sum(seg)
);

endmodule

module full_adder_3bit (
    input [2:0] a,
    input [2:0] b,
    output [3:0] sum,
    output carry_out
);

wire c1, c2;

full_adder fa0 (.a(a[0]), .b(b[0]), .c_in(1'b0), .sum(sum[0]), .c_out(c1));
full_adder fa1 (.a(a[1]), .b(b[1]), .c_in(c1), .sum(sum[1]), .c_out(c2));
full_adder fa2 (.a(a[2]), .b(b[2]), .c_in(c2), .sum(sum[2]), .c_out(carry_out));

assign sum[3] = carry_out;

endmodule

module half_full_adder_3bit (
    input [2:0] a,
    input [2:0] b,
    output [3:0] sum,
    output carry_out
);

wire c1, c2;

half_adder ha0 (.a(a[0]), .b(b[0]), .sum(sum[0]), .c_out(c1));
full_adder fa1 (.a(a[1]), .b(b[1]), .c_in(c1), .sum(sum[1]), .c_out(c2));
full_adder fa2 (.a(a[2]), .b(b[2]), .c_in(c2), .sum(sum[2]), .c_out(carry_out));

assign sum[3] = carry_out;

endmodule

module sum_module (
    input [3:0] sum_full_adder,
    input [3:0] sum_half_full_adder,
    output [6:0] final_sum
);

assign final_sum = sum_full_adder + sum_half_full_adder;

endmodule

module full_adder (
    input a,
    input b,
    input c_in,
    output sum,
    output c_out
);

assign sum = a ^ b ^ c_in;
assign c_out = (a & b) | (a & c_in) | (b & c_in);

endmodule

module half_adder (
    input a,
    input b,
    output sum,
    output c_out
);

assign sum = a ^ b;
assign c_out = a & b;

endmodule