
module mux4to1 (
    input [1:0] sel,
    input [3:0] in0,
    input [3:0] in1,
    input [3:0] in2,
    input [3:0] in3,
    output [3:0] out
);


wire [15:0] priority_enc_out;

priority_encoder pe (
    .in({in3, in2, in1, in0}),
    .out(priority_enc_out)
);

assign out = (sel == 2'b00) ? (priority_enc_out[3:0] & in0) :
              (sel == 2'b01) ? (priority_enc_out[7:4] & in1) :
              (sel == 2'b10) ? (priority_enc_out[11:8] & in2) :
              (priority_enc_out[15:12] & in3);

endmodule
module priority_encoder (
    input [15:0] in,
    output [15:0] out
);

assign out = (in[0] == 1'b1) ? 16'b0000000000000001 :
              (in[1] == 1'b1) ? 16'b0000000000000010 :
              (in[2] == 1'b1) ? 16'b0000000000000100 :
              (in[3] == 1'b1) ? 16'b0000000000001000 :
              (in[4] == 1'b1) ? 16'b0000000000010000 :
              (in[5] == 1'b1) ? 16'b0000000000100000 :
              (in[6] == 1'b1) ? 16'b0000000001000000 :
              (in[7] == 1'b1) ? 16'b0000000010000000 :
              (in[8] == 1'b1) ? 16'b0000000100000000 :
              (in[9] == 1'b1) ? 16'b0000001000000000 :
              (in[10] == 1'b1) ? 16'b0000010000000000 :
              (in[11] == 1'b1) ? 16'b0000100000000000 :
              (in[12] == 1'b1) ? 16'b0001000000000000 :
              (in[13] == 1'b1) ? 16'b0010000000000000 :
              (in[14] == 1'b1) ? 16'b0100000000000000 :
              (in[15] == 1'b1) ? 16'b1000000000000000 :
              16'b1111111111111111;

endmodule