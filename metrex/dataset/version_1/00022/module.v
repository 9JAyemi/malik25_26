








`define RCB_128_SIZE  (128 / 4)
`define RCB_64_SIZE   ( 64 / 4)

module credit_manager #(
  parameter                 MAX_PKTS = 0
)(
  input                     clk,
  input                     rst,


  output        [2:0]       o_fc_sel,             input                     i_rcb_sel,
  input         [7:0]       i_fc_cplh,            input         [11:0]      i_fc_cpld,            output                    o_ready,              input         [9:0]       i_dword_req_count,
  input                     i_cmt_stb,            input         [9:0]       i_dword_rcv_count,
  input                     i_rcv_stb
);

reg             [7:0]       r_hdr_in_flt;
reg             [11:0]      r_dat_in_flt;

wire                        w_hdr_rdy;
wire                        w_dat_rdy;
reg             [7:0]       r_max_hdr_req;

wire            [7:0]       w_hdr_avail;
wire            [11:0]      w_dat_avail;
wire            [15:0]      w_dword_avail;


reg             [7:0]       r_hdr_rcv_size;
reg                         r_delay_rcv_stb;

wire            [11:0]      w_data_credit_req_size;
wire            [11:0]      w_data_credit_rcv_size;


always @ (*) begin
  r_max_hdr_req = 0;
  if (i_rcb_sel) begin
    if (i_dword_req_count < `RCB_128_SIZE) begin
      r_max_hdr_req             =  1;
    end
    else begin
      r_max_hdr_req             =  i_dword_req_count[9:5];
    end
  end
  else begin
    if (i_dword_req_count < `RCB_64_SIZE) begin
      r_max_hdr_req             = 1;
    end
    else begin
      r_max_hdr_req             = i_dword_req_count[9:4];
    end
  end
end


always @ (*) begin
  r_hdr_rcv_size  = 0;
  if (i_rcb_sel) begin
    if (i_dword_rcv_count < `RCB_128_SIZE) begin
      r_hdr_rcv_size            = 1;
    end
    else begin
      r_hdr_rcv_size            =  i_dword_rcv_count[9:5];
    end
  end
  else begin
    if (i_dword_rcv_count < `RCB_64_SIZE) begin
      r_hdr_rcv_size            = 1;
    end
    else begin
      r_hdr_rcv_size            =  i_dword_rcv_count[9:4];
    end
  end
end

assign  w_data_credit_req_size  = (i_dword_req_count[9:2] == 0) ? 10'h1  : i_dword_req_count[9:2];
assign  w_data_credit_rcv_size  = (i_dword_rcv_count[9:2] == 0) ? 10'h1  : i_dword_rcv_count[9:2];

assign  w_hdr_avail             = (i_fc_cplh - r_hdr_in_flt);
assign  w_dat_avail             = (i_fc_cpld - r_dat_in_flt);
assign  w_dword_avail           = {w_dat_avail, 2'b00};

assign  w_hdr_rdy               = (w_hdr_avail > r_max_hdr_req);
assign  w_dat_rdy               = (w_dat_avail > w_data_credit_req_size);

assign  o_fc_sel                = 3'h0;

assign  o_ready                 = (MAX_PKTS == 0) ?
                                     (w_hdr_rdy & w_dat_rdy) :
                                    ((w_hdr_rdy & w_dat_rdy) && ((r_hdr_in_flt >> 3) <= MAX_PKTS));

always  @ (posedge clk) begin
  if (rst) begin
    r_hdr_in_flt                <=  0;
    r_dat_in_flt                <=  0;
    r_delay_rcv_stb             <=  0;
  end
  else begin
    if (i_cmt_stb) begin
      r_hdr_in_flt              <=  r_hdr_in_flt + r_max_hdr_req;
      r_dat_in_flt              <=  r_dat_in_flt + w_data_credit_req_size;
      if (i_rcv_stb) begin
        r_delay_rcv_stb         <=  1;
      end
    end
    else if (i_rcv_stb || r_delay_rcv_stb) begin
      r_delay_rcv_stb           <=  0;
      r_hdr_in_flt              <=  r_hdr_in_flt - r_hdr_rcv_size;
      r_dat_in_flt              <=  r_dat_in_flt - w_data_credit_rcv_size;
    end
  end
end

endmodule
