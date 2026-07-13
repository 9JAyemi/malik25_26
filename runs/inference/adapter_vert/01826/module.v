
module hls_contrast_streibs(
    input [din0_WIDTH - 1:0] din0,
    input [din1_WIDTH - 1:0] din1,
    input [din2_WIDTH - 1:0] din2,
    output[dout_WIDTH - 1:0] dout);

parameter ID = 32'd1;
parameter NUM_STAGE = 32'd1;
parameter din0_WIDTH = 32'd1;
parameter din1_WIDTH = 32'd1;
parameter din2_WIDTH = 32'd1;
parameter dout_WIDTH = 32'd1;

hls_contrast_streibs_DSP48_6 #(
    .ID ( ID ),
    .NUM_STAGE ( NUM_STAGE ),
    .din0_WIDTH ( din0_WIDTH ),
    .din1_WIDTH ( din1_WIDTH ),
    .din2_WIDTH ( din2_WIDTH ),
    .dout_WIDTH ( dout_WIDTH ))
hls_contrast_streibs_DSP48_6_U (
    .din0 ( din0 ),
    .din1 ( din1 ),
    .din2 ( din2 ),
    .dout ( dout ));
endmodule
module hls_contrast_streibs_DSP48_6 (
    input  [din0_WIDTH - 1:0] din0,
    input  [din1_WIDTH - 1:0] din1,
    input  [din2_WIDTH - 1:0] din2,
    output [dout_WIDTH - 1:0] dout);

parameter ID = 32'd1;
parameter NUM_STAGE = 32'd1;
parameter din0_WIDTH = 32'd1;
parameter din1_WIDTH = 32'd1;
parameter din2_WIDTH = 32'd1;
parameter dout_WIDTH = 32'd1;

wire [dout_WIDTH - 1:0] tmp_mul;
wire [dout_WIDTH - 1:0] acc_result;

assign tmp_mul = din0 * din1;
assign acc_result = tmp_mul + din2;
assign dout = acc_result;

endmodule