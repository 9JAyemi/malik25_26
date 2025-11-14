
module full_adder(
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

wire temp_sum;
wire temp_cout;

assign {temp_cout, temp_sum} = a + b + cin;
assign sum = temp_sum;
assign cout = temp_cout;

endmodule

module top_module(
    input clk,
    input [31:0] a,
    input [31:0] b,
    input sub,
    output [31:0] sum
);

reg [31:0] a_reg, b_reg;
wire [31:0] a_xor_b;
wire [31:0] sub_xor_sum;
wire [31:0] sub_and_b;
wire [31:0] sub_and_sum;
wire [31:0] sub_and_cin;
wire [31:0] cin;

full_adder fa[31:0](
    .a(a_xor_b),
    .b(sub_and_cin),
    .cin(cin),
    .sum(sum),
    .cout()
);

always @(posedge clk) begin
    a_reg <= a;
    b_reg <= b;
end

assign a_xor_b = a_reg ^ b_reg;

assign sub_xor_sum = sub ^ sum;

assign sub_and_b = sub & b_reg;

assign sub_and_sum = sub & sum;

assign sub_and_cin = sub_and_b | sub_and_sum;

assign cin = {32{sub}};

endmodule
