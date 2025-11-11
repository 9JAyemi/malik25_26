
module verilog_mult_32bit
#(parameter
    ID         = 1,
    NUM_STAGE  = 4,
    din0_WIDTH = 32,
    din1_WIDTH = 32,
    dout_WIDTH = 32
)(
    input  wire                  clk,
    input  wire                  reset,
    input  wire                  ce,
    input  wire [din0_WIDTH-1:0] din0,
    input  wire [din1_WIDTH-1:0] din1,
    output wire [dout_WIDTH-1:0] dout
);

wire                  aclk;
wire                  aclken;
wire                  a_tvalid;
wire [31:0]           a_tdata;
wire                  b_tvalid;
wire [31:0]           b_tdata;
wire                  r_tvalid;
wire [31:0]           r_tdata;
reg  [din0_WIDTH-1:0] din0_buf1;
reg  [din1_WIDTH-1:0] din1_buf1;

HLS_accel_fmul_32ns_32ns_32_4_max_dsp #(
    .ID(ID),
    .NUM_STAGE(NUM_STAGE),
    .din0_WIDTH(din0_WIDTH),
    .din1_WIDTH(din1_WIDTH),
    .dout_WIDTH(dout_WIDTH)
) HLS_accel_fmul_32ns_32ns_32_4_max_dsp_u (
    .aclk(aclk),
    .aclken(aclken),
    .a_tvalid(a_tvalid),
    .a_tdata(a_tdata),
    .b_tvalid(b_tvalid),
    .b_tdata(b_tdata),
    .r_tvalid(r_tvalid),
    .r_tdata(r_tdata)
);

assign aclk     = clk;
assign aclken   = ce;
assign a_tvalid = 1'b1;
assign a_tdata  = din0_buf1;
assign b_tvalid = 1'b1;
assign b_tdata  = din1_buf1;
assign dout     = r_tdata;

always @(posedge clk) begin
    if (ce) begin
        din0_buf1 <= din0;
        din1_buf1 <= din1;
    end
end

endmodule
module HLS_accel_fmul_32ns_32ns_32_4_max_dsp
#(parameter
    ID         = 1,
    NUM_STAGE  = 4,
    din0_WIDTH = 32,
    din1_WIDTH = 32,
    dout_WIDTH = 32
)(
    input  wire                  aclk,
    input  wire                  aclken,
    input  wire                  a_tvalid,
    input  wire [din0_WIDTH-1:0] a_tdata,
    input  wire                  b_tvalid,
    input  wire [din1_WIDTH-1:0] b_tdata,
    output wire                  r_tvalid,
    output wire [dout_WIDTH-1:0] r_tdata
);

reg                   a_tvalid_1;
reg  [din0_WIDTH-1:0] a_tdata_1;
reg                   b_tvalid_1;
reg  [din1_WIDTH-1:0] b_tdata_1;
reg  [dout_WIDTH-1:0] r_tdata;
wire                  ap_ce_reg;

always @(*) begin
    if (aclken) begin
        a_tvalid_1  <= a_tvalid;
        a_tdata_1   <= a_tdata;
        b_tvalid_1  <= b_tvalid;
        b_tdata_1   <= b_tdata;
    end
end

always @(posedge aclk) begin
    if (aclken) begin
        r_tdata <= a_tdata_1 * b_tdata_1;
    end
end

assign ap_ce_reg = 1'b1;

assign r_tvalid = a_tvalid_1 & b_tvalid_1;

endmodule