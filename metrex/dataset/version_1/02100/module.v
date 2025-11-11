
module parity_bit (
    input [7:0] in,
    output wire parity
);

wire [3:0] and_out;
wire xor_out;

assign and_out = in[7:4] & in[3:0];
assign xor_out = in[7] ^ in[6] ^ in[5] ^ in[4] ^ in[3] ^ in[2] ^ in[1] ^ in[0];

assign parity = and_out[3] & and_out[2] & and_out[1] & and_out[0] & xor_out;

endmodule

module combinational_logic (
    input [3:0] in,
    output wire [3:0] out_logic
);

assign out_logic[0] = in[0] & in[1];
assign out_logic[1] = in[1] | in[2];
assign out_logic[2] = in[2] ^ in[3];
assign out_logic[3] = in[0] & in[3];

endmodule

module sum_computation (
    input parity,
    input [3:0] xor_out,
    output wire [3:0] sum
);

assign sum = (parity + xor_out) % 16;

endmodule

module top_module (
    input [7:0] in,
    output wire [3:0] out_logic
);

wire parity;
wire [3:0] xor_out;
wire [3:0] sum;

parity_bit parity_bit_inst (
    .in(in),
    .parity(parity)
);

combinational_logic combinational_logic_inst (
    .in({in[4], in[5], in[6], in[7]}),
    .out_logic(xor_out)
);

sum_computation sum_computation_inst (
    .parity(parity),
    .xor_out(xor_out),
    .sum(sum)
);

assign out_logic = sum;

endmodule
