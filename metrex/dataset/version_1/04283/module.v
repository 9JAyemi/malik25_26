

module axi_traffic_gen_v2_0_7_axis_fifo
  #(
parameter WIDTH        = 33,
parameter HEADREG      = 1 ,
parameter ZERO_INVALID = 1 ,
parameter FULL_LEVEL   = 14,
parameter DEPTH        = 16,
parameter DEPTHBITS    = 4
  ) (
input Clk                        ,
input Rst_n                      ,

input [WIDTH-1:0] in_data        ,
input [WIDTH-1:0] in_invalid_data,
input  in_push                   ,
input  in_ready                  ,
input  in_block_notfull          ,
input  in_block_outvalid         ,
output  out_valid                ,
output  out_notfull              ,
output  out_overflow             ,
output [DEPTHBITS-1:0] out_depth ,
output [WIDTH-1:0] out_data
);

 reg [WIDTH-1:0] data_ff[DEPTH-1:0]               ;
reg [WIDTH-1:0] headreg_ff                       ;
reg [DEPTHBITS-1:0] in_ptr_ff, out_ptr_ff        ;
reg [DEPTHBITS:0] depth_ff                       ;
reg  valid_ff, full_ff, notfull_ff, valid_filt_ff;

wire do_pop = in_ready && valid_filt_ff;
wire [DEPTHBITS-1:0] in_ptr = (in_push) ? in_ptr_ff[DEPTHBITS-1:0] + 'h1 :
            in_ptr_ff[DEPTHBITS-1:0];
wire [DEPTHBITS:0] depth =
    (in_push && ~do_pop) ? depth_ff[DEPTHBITS:0] + 'h1 :
    (~in_push && do_pop) ? depth_ff[DEPTHBITS:0] - 'h1 :
              depth_ff[DEPTHBITS:0];

wire  depth_was1 = (depth_ff[DEPTHBITS:0] == 'h1);
wire  valid      = (depth[DEPTHBITS:0] != 'h0);
wire  full       = (depth[DEPTHBITS:0] >= FULL_LEVEL) || in_block_notfull;
wire  notfull    = ~full;

wire [WIDTH-1:0] raw_data = data_ff[out_ptr_ff[DEPTHBITS-1:0]];
wire [DEPTHBITS-1:0] out_ptr = (do_pop) ? out_ptr_ff[DEPTHBITS-1:0] + 'h1 :
            out_ptr_ff[DEPTHBITS-1:0];
wire [WIDTH-1:0] head_raw_data = (depth_was1) ? in_data[WIDTH-1:0] :
          raw_data[WIDTH-1:0];
wire [WIDTH-1:0] headreg = (!valid_ff && in_push) ? in_data[WIDTH-1:0] :
    (do_pop) ? head_raw_data[WIDTH-1:0] :
              headreg_ff[WIDTH-1:0];
wire  valid_filt = valid &&
      ((valid_filt_ff && ~do_pop) || ~in_block_outvalid);

always @(posedge Clk) begin
  in_ptr_ff[DEPTHBITS-1:0]  <= (Rst_n) ? in_ptr[DEPTHBITS-1:0] : 'h0;
  out_ptr_ff[DEPTHBITS-1:0] <= (Rst_n) ? out_ptr[DEPTHBITS-1:0] : ((HEADREG) ? 'h1 : 'h0);
  depth_ff[DEPTHBITS:0]     <= (Rst_n) ? depth[DEPTHBITS:0] : 'h0;
  valid_ff                  <= (Rst_n) ? valid : 1'b0;
  valid_filt_ff             <= (Rst_n) ? valid_filt : 1'b0;
  full_ff                   <= (Rst_n) ? full : 1'b0;
  notfull_ff                <= (Rst_n) ? notfull : 1'b0;
  headreg_ff[WIDTH-1:0]     <= (Rst_n) ? headreg[WIDTH-1:0] : 'h0;
end

integer i;
always @(posedge Clk) begin
  if(in_push) begin
    data_ff[in_ptr_ff[DEPTHBITS-1:0]] <= in_data[WIDTH-1:0];
  end
end

wire [WIDTH-1:0] out_data_pre = (HEADREG) ? headreg_ff[WIDTH-1:0] :
              raw_data[WIDTH-1:0];
assign out_data[WIDTH-1:0]    = (ZERO_INVALID && ~valid_filt_ff) ?
      in_invalid_data[WIDTH-1:0] : out_data_pre[WIDTH-1:0];
assign out_valid              = valid_filt_ff;
assign out_notfull            = notfull_ff;
assign out_overflow           = depth_ff[DEPTHBITS];
assign out_depth              = depth_ff[DEPTHBITS-1:0];

endmodule
