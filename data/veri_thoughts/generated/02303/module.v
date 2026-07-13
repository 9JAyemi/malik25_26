module ll_axis_bridge #
(
    parameter DATA_WIDTH = 8
)
(
    input  wire                   clk,
    input  wire                   rst,
    
    
    input  wire [DATA_WIDTH-1:0]  ll_data_in,
    input  wire                   ll_sof_in_n,
    input  wire                   ll_eof_in_n,
    input  wire                   ll_src_rdy_in_n,
    output wire                   ll_dst_rdy_out_n,
    
    
    output wire [DATA_WIDTH-1:0]  axis_tdata,
    output wire                   axis_tvalid,
    input  wire                   axis_tready,
    output wire                   axis_tlast
);

assign axis_tdata = ll_data_in;
assign axis_tvalid = ~ll_src_rdy_in_n;
assign axis_tlast = ~ll_eof_in_n;

assign ll_dst_rdy_out_n = ~axis_tready;

endmodule