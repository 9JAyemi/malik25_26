
module add_sub_pipeline(
    input [31:0] a,
    input [31:0] b,
    input sub,
    input clk,
    output [31:0] sum
);

reg [31:0] a_reg, b_reg;
wire [31:0] sum_reg;
wire [31:0] carry_in, carry_out;
wire [31:0] a_xor_b;

assign a_xor_b = (sub == 1'b1) ? ~b : b;

assign carry_in = sub;

adder_pipeline adder_pipeline_inst(
    .a(a_reg),
    .b(a_xor_b),
    .carry_in(carry_in),
    .sum(sum_reg),
    .carry_out(carry_out)
);

assign sum = sum_reg;

always @(posedge clk) begin
    a_reg <= a;
    b_reg <= b;
end

endmodule

module adder_pipeline(
    input [31:0] a,
    input [31:0] b,
    input [31:0] carry_in,
    output [31:0] sum,
    output [31:0] carry_out
);

genvar i;
wire [31:0] p, g;

generate
    for (i = 0; i < 32; i = i + 1) begin : gen_loop1
        assign p[i] = a[i] ^ b[i];
        assign g[i] = a[i] & b[i];
    end
endgenerate

assign sum[0] = p[0] ^ carry_in;
assign carry_out[0] = g[0] | (p[0] & carry_in);

generate
    for (i = 1; i < 32; i = i + 1) begin : gen_loop2
        assign sum[i] = p[i] ^ carry_out[i-1];
        assign carry_out[i] = g[i] | (p[i] & carry_out[i-1]);
    end
endgenerate

endmodule
