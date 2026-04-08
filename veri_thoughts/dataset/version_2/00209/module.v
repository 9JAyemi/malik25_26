
module top_module(
    input [99:0] in,
    input [3:0] in1,
    input [3:0] in2,
    input select,
    output out_and,
    output out_or,
    output out_xor
);

// First module - 100-input AND gate using 4-input AND gates
wire [24:0] and_out;
assign and_out[0] = in[0] & in[1] & in[2] & in[3];
assign and_out[1] = in[4] & in[5] & in[6] & in[7];
assign and_out[2] = in[8] & in[9] & in[10] & in[11];
assign and_out[3] = in[12] & in[13] & in[14] & in[15];
assign and_out[4] = in[16] & in[17] & in[18] & in[19];
assign and_out[5] = in[20] & in[21] & in[22] & in[23];
assign and_out[6] = in[24] & in[25] & in[26] & in[27];
assign and_out[7] = in[28] & in[29] & in[30] & in[31];
assign and_out[8] = in[32] & in[33] & in[34] & in[35];
assign and_out[9] = in[36] & in[37] & in[38] & in[39];
assign and_out[10] = in[40] & in[41] & in[42] & in[43];
assign and_out[11] = in[44] & in[45] & in[46] & in[47];
assign and_out[12] = in[48] & in[49] & in[50] & in[51];
assign and_out[13] = in[52] & in[53] & in[54] & in[55];
assign and_out[14] = in[56] & in[57] & in[58] & in[59];
assign and_out[15] = in[60] & in[61] & in[62] & in[63];
assign and_out[16] = in[64] & in[65] & in[66] & in[67];
assign and_out[17] = in[68] & in[69] & in[70] & in[71];
assign and_out[18] = in[72] & in[73] & in[74] & in[75];
assign and_out[19] = in[76] & in[77] & in[78] & in[79];
assign and_out[20] = in[80] & in[81] & in[82] & in[83];
assign and_out[21] = in[84] & in[85] & in[86] & in[87];
assign and_out[22] = in[88] & in[89] & in[90] & in[91];
assign and_out[23] = in[92] & in[93] & in[94] & in[95];
assign and_out[24] = in[96] & in[97] & in[98] & in[99];

// Second module - logical operations on 4-bit binary numbers
wire [3:0] and_out_1;
wire [3:0] or_out_1;
wire [3:0] xor_out_1;
wire [3:0] and_out_2;
wire [3:0] or_out_2;
wire [3:0] xor_out_2;

and_module and1(.in1(in1), .in2(in2), .out(and_out_1));
or_module or1(.in1(in1), .in2(in2), .out(or_out_1));
xor_module xor1(.in1(in1), .in2(in2), .out(xor_out_1));
and_module and2(.in1(in1), .in2(in2), .out(and_out_2));
or_module or2(.in1(in1), .in2(in2), .out(or_out_2));
xor_module xor2(.in1(in1), .in2(in2), .out(xor_out_2));

// Third module - select between AND and OR operations on the outputs of the two given modules
wire [3:0] final_out;
assign final_out = (select == 1) ? (and_out_1 & and_out_2) : (or_out_1 | or_out_2);

// Assign outputs
assign out_and = and_out[0] & and_out[1] & and_out[2] & and_out[3] & and_out[4] & and_out[5] & and_out[6] & and_out[7] & and_out[8] & and_out[9] & and_out[10] & and_out[11] & and_out[12] & and_out[13] & and_out[14] & and_out[15] & and_out[16] & and_out[17] & and_out[18] & and_out[19] & and_out[20] & and_out[21] & and_out[22] & and_out[23] & and_out[24];
assign out_or = final_out[0] | final_out[1] | final_out[2] | final_out[3];
assign out_xor = (xor_out_1[0] ^ xor_out_1[1]) ^ (xor_out_1[2] ^ xor_out_1[3]);

endmodule
module and_module(
    input [3:0] in1,
    input [3:0] in2,
    output [3:0] out
);
assign out = in1 & in2;
endmodule
module or_module(
    input [3:0] in1,
    input [3:0] in2,
    output [3:0] out
);
assign out = in1 | in2;
endmodule
module xor_module(
    input [3:0] in1,
    input [3:0] in2,
    output [3:0] out
);
assign out = in1 ^ in2;
endmodule