
module bitwise_or_and_adder(
    input  [15:0] in1,
    input  [15:0] in2,
    output [16:0] res
);

// Bitwise OR operation
assign res[0] = in1[0] | in2[0];
assign res[1] = in1[1] | in2[1];
assign res[2] = in1[2] | in2[2];
assign res[3] = in1[3] | in2[3];
assign res[4] = in1[4] | in2[4];
assign res[5] = in1[5] | in2[5];
assign res[6] = in1[6] | in2[6];
assign res[7] = in1[7] | in2[7];
assign res[8] = in1[8] | in2[8];
assign res[9] = in1[9] | in2[9];
assign res[10] = in1[10] | in2[10];
assign res[11] = in1[11] | in2[11];
assign res[12] = in1[12] | in2[12];
assign res[13] = in1[13] | in2[13];
assign res[14] = in1[14] | in2[14];
assign res[15] = in1[15] | in2[15];
assign res[16] = 0;

endmodule