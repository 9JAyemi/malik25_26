
module comb_circuit(
    input [99:0] in,
    output out_and,
    output out_or,
    output out_xor
);

wire [49:0] and_out;
wire [49:0] or_out;
wire [98:0] xor_out;

// AND gates
genvar i;
generate
    for (i = 0; i < 50; i = i + 1) begin : and_gates
        assign and_out[i] = in[2*i] & in[2*i+1];
    end
endgenerate

// OR gates
generate
    for (i = 0; i < 50; i = i + 1) begin : or_gates
        assign or_out[i] = in[2*i] | in[2*i+1];
    end
endgenerate

// XOR gates
generate
    for (i = 0; i < 99; i = i + 1) begin : xor_gates
        assign xor_out[i] = in[i] ^ in[i+1];
    end
endgenerate

// AND of all inputs
and and_all (
    .a(and_out),
    .y(out_and)
);

// OR of all inputs
or or_all (
    .a(or_out),
    .y(out_or)
);

// XOR of all inputs
assign out_xor = xor_out[0] ^ xor_out[1] ^ xor_out[2] ^ xor_out[3] ^ xor_out[4] ^ xor_out[5] ^ xor_out[6] ^ xor_out[7] ^ xor_out[8] ^ xor_out[9] ^ xor_out[10] ^ xor_out[11] ^ xor_out[12] ^ xor_out[13] ^ xor_out[14] ^ xor_out[15] ^ xor_out[16] ^ xor_out[17] ^ xor_out[18] ^ xor_out[19] ^ xor_out[20] ^ xor_out[21] ^ xor_out[22] ^ xor_out[23] ^ xor_out[24] ^ xor_out[25] ^ xor_out[26] ^ xor_out[27] ^ xor_out[28] ^ xor_out[29] ^ xor_out[30] ^ xor_out[31] ^ xor_out[32] ^ xor_out[33] ^ xor_out[34] ^ xor_out[35] ^ xor_out[36] ^ xor_out[37] ^ xor_out[38] ^ xor_out[39] ^ xor_out[40] ^ xor_out[41] ^ xor_out[42] ^ xor_out[43] ^ xor_out[44] ^ xor_out[45] ^ xor_out[46] ^ xor_out[47] ^ xor_out[48] ^ xor_out[49] ^ xor_out[50] ^ xor_out[51] ^ xor_out[52] ^ xor_out[53] ^ xor_out[54] ^ xor_out[55] ^ xor_out[56] ^ xor_out[57] ^ xor_out[58] ^ xor_out[59] ^ xor_out[60] ^ xor_out[61] ^ xor_out[62] ^ xor_out[63] ^ xor_out[64] ^ xor_out[65] ^ xor_out[66] ^ xor_out[67] ^ xor_out[68] ^ xor_out[69] ^ xor_out[70] ^ xor_out[71] ^ xor_out[72] ^ xor_out[73] ^ xor_out[74] ^ xor_out[75] ^ xor_out[76] ^ xor_out[77] ^ xor_out[78] ^ xor_out[79] ^ xor_out[80] ^ xor_out[81] ^ xor_out[82] ^ xor_out[83] ^ xor_out[84] ^ xor_out[85] ^ xor_out[86] ^ xor_out[87] ^ xor_out[88] ^ xor_out[89] ^ xor_out[90] ^ xor_out[91] ^ xor_out[92] ^ xor_out[93] ^ xor_out[94] ^ xor_out[95] ^ xor_out[96] ^ xor_out[97] ^ xor_out[98];

endmodule