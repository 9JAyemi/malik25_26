// SystemVerilog Assertions for rx_engine
// Bind-friendly SVA module. Focused, high-signal-coverage checks and covers.

module rx_engine_sva #(
  parameter int C_DATA_WIDTH = 64
)(
  input  logic                      clk_i,
  input  logic                      rst_n,

  // AXI-Stream RX
  input  logic [C_DATA_WIDTH-1:0]   m_axis_rx_tdata,
  input  logic                      m_axis_rx_tlast,
  input  logic                      m_axis_rx_tvalid,
  input  logic                      m_axis_rx_tready,

  // DUT outputs/inputs
  input  logic                      compl_done_i,
  input  logic                      req_compl_wd_o,
  input  logic [31:0]               tx_reg_data_o,

  input  logic [2:0]                req_tc_o,
  input  logic                      req_td_o,
  input  logic                      req_ep_o,
  input  logic [1:0]                req_attr_o,
  input  logic [9:0]                req_len_o,
  input  logic [15:0]               req_rid_o,
  input  logic [7:0]                req_tag_o,
  input  logic [6:0]                req_addr_o,

  input  logic [31:0]               reg_data_o,
  input  logic                      reg_data_valid_o,
  input  logic [9:0]                reg_addr_o,

  input  logic                      fpga_reg_rd_o,
  input  logic [31:0]               reg_data_i,
  input  logic                      fpga_reg_rd_ack_i,

  input  logic [31:0]               user_data_o,
  input  logic [19:0]               user_addr_o,
  input  logic                      user_wr_req_o,
  input  logic [31:0]               user_data_i,
  input  logic                      user_rd_ack_i,
  input  logic                      user_rd_req_o,

  input  logic [63:0]               rcvd_data_o,
  input  logic                      rcvd_data_valid_o,
  input  logic [7:0]                cpld_tag_o,

  // Internal DUT signals (bind to internals)
  input  logic [2:0]                state,
  input  logic                      sop,
  input  logic                      in_packet_q,
  input  logic                      rcv_data,
  input  logic                      user_wr_ack,
  input  logic [31:0]               rx_tdata_p,
  input  logic                      lock_tag
);

  // Mirror DUT localparams
  localparam int unsigned IDLE           = 'd0;
  localparam int unsigned SEND_DATA      = 'd1;
  localparam int unsigned WAIT_FPGA_DATA = 'd2;
  localparam int unsigned WAIT_USR_DATA  = 'd3;
  localparam int unsigned WAIT_TX_ACK    = 'd4;
  localparam int unsigned WR_DATA        = 'd5;
  localparam int unsigned RX_DATA        = 'd6;

  localparam logic [6:0] MEM_RD = 7'b0000000;
  localparam logic [6:0] MEM_WR = 7'b1000000;
  localparam logic [6:0] CPLD   = 7'b1001010;

  localparam int unsigned A_MAX = 'h0400;

  default clocking cb @ (posedge clk_i); endclocking
  default disable iff (!rst_n);

  // Reset values
  always @(posedge clk_i) if (!rst_n) begin
    assert (state == IDLE);
    assert (m_axis_rx_tready == 1'b0);
    assert (!req_compl_wd_o && !user_rd_req_o && !user_wr_req_o && !fpga_reg_rd_o && !reg_data_valid_o);
  end

  // SOP/in-packet bookkeeping
  assert property (sop == (!in_packet_q && m_axis_rx_tvalid));
  assert property ((sop && m_axis_rx_tready) |=> in_packet_q);
  assert property ((m_axis_rx_tvalid && m_axis_rx_tready && m_axis_rx_tlast) |=> !in_packet_q);

  // Ready policy
  assert property (state == IDLE |-> m_axis_rx_tready);

  // Decode-driven state transitions from IDLE
  assert property (state==IDLE && sop && m_axis_rx_tready && m_axis_rx_tdata[30:24]==MEM_RD |=> state==SEND_DATA);
  assert property (state==IDLE && sop && m_axis_rx_tready && m_axis_rx_tdata[30:24]==MEM_WR |=> state==WR_DATA);
  assert property (state==IDLE && sop && m_axis_rx_tready && m_axis_rx_tdata[30:24]==CPLD   |=> state==RX_DATA);

  // Header fields captured on SOP (next cycle view)
  assert property (sop && m_axis_rx_tready |=> 
      req_len_o  == $past(m_axis_rx_tdata[9:0])     &&
      req_attr_o == $past(m_axis_rx_tdata[13:12])   &&
      req_ep_o   == $past(m_axis_rx_tdata[14])      &&
      req_td_o   == $past(m_axis_rx_tdata[15])      &&
      req_tc_o   == $past(m_axis_rx_tdata[22:20])   &&
      req_tag_o  == $past(m_axis_rx_tdata[47:40])   &&
      req_rid_o  == $past(m_axis_rx_tdata[63:48])
  );

  // SEND_DATA branch to FPGA/USR read paths
  assert property (state==SEND_DATA && m_axis_rx_tvalid && m_axis_rx_tlast && (m_axis_rx_tdata[21:0] < A_MAX)
                   |=> state==WAIT_FPGA_DATA && !m_axis_rx_tready && !fpga_reg_rd_o);
  assert property (state==SEND_DATA && m_axis_rx_tvalid && m_axis_rx_tlast && !(m_axis_rx_tdata[21:0] < A_MAX)
                   |=> state==WAIT_USR_DATA &&  m_axis_rx_tready==m_axis_rx_tready && user_rd_req_o);

  // READ: FPGA path ack -> completion
  assert property (state==WAIT_FPGA_DATA && fpga_reg_rd_ack_i
                   |=> state==WAIT_TX_ACK && req_compl_wd_o && tx_reg_data_o == $past(reg_data_i));
  // READ: USR path ack -> completion
  assert property (state==WAIT_USR_DATA && user_rd_ack_i
                   |=> state==WAIT_TX_ACK && req_compl_wd_o && tx_reg_data_o == $past(user_data_i) && !user_rd_req_o);

  // Completion window holds until TX done
  assert property ($rose(req_compl_wd_o) |-> (req_compl_wd_o until compl_done_i));
  assert property (state==WAIT_TX_ACK && compl_done_i |=> state==IDLE && !req_compl_wd_o && m_axis_rx_tready);

  // Write data capture on WR_DATA accept (next-cycle view)
  assert property (state==WR_DATA && m_axis_rx_tvalid && m_axis_rx_tlast
                   |=> reg_data_o==$past(m_axis_rx_tdata[63:32]) &&
                       user_data_o==$past(m_axis_rx_tdata[63:32]) &&
                       reg_addr_o==$past(m_axis_rx_tdata[9:0])   &&
                       user_addr_o==$past(m_axis_rx_tdata[19:0]));

  // Write targeting and strobes
  assert property ($rose(reg_data_valid_o) |-> $past(state==WR_DATA && m_axis_rx_tvalid && m_axis_rx_tlast && (m_axis_rx_tdata[21:0] < A_MAX)));
  assert property ($rose(user_wr_req_o)    |-> $past(state==WR_DATA && m_axis_rx_tvalid && m_axis_rx_tlast && !(m_axis_rx_tdata[21:0] < A_MAX)));
  assert property (!(reg_data_valid_o && user_wr_req_o));

  // Write user path should exit next cycle via user_wr_ack
  assert property ($rose(user_wr_req_o) |=> state==IDLE);

  // Read request pulses origin
  assert property ($rose(fpga_reg_rd_o) |-> $past(state)==SEND_DATA);
  // USR read request must persist until ack
  assert property (state==WAIT_USR_DATA |-> user_rd_req_o);
  assert property ($rose(user_rd_req_o) |-> user_rd_req_o until user_rd_ack_i);

  // RX_DATA streaming: valid flag and datapath correctness
  assert property (rcvd_data_valid_o == (rcv_data && m_axis_rx_tvalid));
  assert property (rcvd_data_valid_o |-> rcvd_data_o == {$past(m_axis_rx_tdata[63:32]), m_axis_rx_tdata[31:0]});
  assert property (rcv_data |-> state==RX_DATA);
  assert property (rcvd_data_valid_o |-> state==RX_DATA);

  // RX_DATA termination
  assert property (state==RX_DATA && m_axis_rx_tvalid && m_axis_rx_tlast |=> state==IDLE && m_axis_rx_tready);

  // CPLD tag lock pulse behavior (lock toggles 1 then 0)
  assert property (state==IDLE && sop && m_axis_rx_tready && m_axis_rx_tdata[30:24]==CPLD |=> lock_tag);
  assert property ($rose(lock_tag) |=> !lock_tag);

  // Completion payload stability while req_compl_wd_o asserted
  assert property (req_compl_wd_o |-> $stable(tx_reg_data_o));

  // Address/control capture on SEND_DATA accept (next-cycle view)
  assert property (state==SEND_DATA && m_axis_rx_tvalid && m_axis_rx_tlast
                   |=> req_addr_o==$past(m_axis_rx_tdata[6:0]) &&
                       reg_addr_o==$past(m_axis_rx_tdata[9:0]) &&
                       user_addr_o==$past(m_axis_rx_tdata[19:0]));

  // Coverage
  cover property ($rose(fpga_reg_rd_o) ##[1:10] fpga_reg_rd_ack_i ##1 req_compl_wd_o ##[1:10] compl_done_i);
  cover property ($rose(user_rd_req_o) ##[1:10] user_rd_ack_i      ##1 req_compl_wd_o ##[1:10] compl_done_i);
  cover property ($rose(reg_data_valid_o) ##[1:10] fpga_reg_wr_ack_i ##1 state==IDLE);
  cover property ($rose(user_wr_req_o) ##1 state==IDLE);
  cover property (state==IDLE && sop && m_axis_rx_tready && m_axis_rx_tdata[30:24]==CPLD ##1 state==RX_DATA ##[1:5] rcvd_data_valid_o ##1 (m_axis_rx_tvalid && m_axis_rx_tlast) ##1 state==IDLE);
  cover property (sop && m_axis_rx_tready ##[1:20] compl_done_i ##1 sop && m_axis_rx_tready); // back-to-back packets
endmodule

// Bind example (connect internal signals; edit names if your tool requires hierarchical paths)
bind rx_engine rx_engine_sva #(.C_DATA_WIDTH(C_DATA_WIDTH)) rx_engine_sva_i (
  .clk_i(clk_i),
  .rst_n(rst_n),

  .m_axis_rx_tdata(m_axis_rx_tdata),
  .m_axis_rx_tlast(m_axis_rx_tlast),
  .m_axis_rx_tvalid(m_axis_rx_tvalid),
  .m_axis_rx_tready(m_axis_rx_tready),

  .compl_done_i(compl_done_i),
  .req_compl_wd_o(req_compl_wd_o),
  .tx_reg_data_o(tx_reg_data_o),

  .req_tc_o(req_tc_o),
  .req_td_o(req_td_o),
  .req_ep_o(req_ep_o),
  .req_attr_o(req_attr_o),
  .req_len_o(req_len_o),
  .req_rid_o(req_rid_o),
  .req_tag_o(req_tag_o),
  .req_addr_o(req_addr_o),

  .reg_data_o(reg_data_o),
  .reg_data_valid_o(reg_data_valid_o),
  .reg_addr_o(reg_addr_o),

  .fpga_reg_rd_o(fpga_reg_rd_o),
  .reg_data_i(reg_data_i),
  .fpga_reg_rd_ack_i(fpga_reg_rd_ack_i),

  .user_data_o(user_data_o),
  .user_addr_o(user_addr_o),
  .user_wr_req_o(user_wr_req_o),
  .user_data_i(user_data_i),
  .user_rd_ack_i(user_rd_ack_i),
  .user_rd_req_o(user_rd_req_o),

  .rcvd_data_o(rcvd_data_o),
  .rcvd_data_valid_o(rcvd_data_valid_o),
  .cpld_tag_o(cpld_tag_o),

  // internals
  .state(state),
  .sop(sop),
  .in_packet_q(in_packet_q),
  .rcv_data(rcv_data),
  .user_wr_ack(user_wr_ack),
  .rx_tdata_p(rx_tdata_p),
  .lock_tag(lock_tag)
);