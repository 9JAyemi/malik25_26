
module combinational_circuit (
    input [49:0] in,
    output out_and,
    output out_or,
    output out_xor
);

wire [24:0] and_out;
wire [24:0] or_out;
wire [48:0] xor_out;

genvar i;
generate
    for (i = 0; i < 25; i = i + 1) begin : and_gates
        assign and_out[i] = in[2*i] & in[2*i+1];
    end

    for (i = 0; i < 25; i = i + 1) begin : or_gates
        assign or_out[i] = in[2*i] | in[2*i+1];
    end

    for (i = 0; i < 49; i = i + 1) begin : xor_gates
        assign xor_out[i] = in[i] ^ in[i+1];
    end
endgenerate

assign out_and = and_out[24];
assign out_or = or_out[24];
assign out_xor = xor_out[48];

endmodule
module shift_register_adder (
    input [49:0] in,
    output out_and,
    output out_or,
    output out_xor,
    input [1:0] shift,
    output [15:0] sum_output
);

wire [49:0] shifted_in;
wire [15:0] shifted_sum;

combinational_circuit comb_inst (
    .in(shifted_in),
    .out_and(out_and),
    .out_or(out_or),
    .out_xor(out_xor)
);

assign shifted_in = in << shift; 
assign shifted_sum = shifted_in + out_xor;

assign sum_output = shifted_sum;

endmodule