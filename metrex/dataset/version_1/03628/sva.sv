// SVA for pcie_core_axi_basic_rx_null_gen
// Bindable, concise, checks key protocol/logic and provides coverage.

module pcie_core_axi_basic_rx_null_gen_sva #(
  parameter int C_DATA_WIDTH = 128,
  parameter int KEEP_WIDTH   = C_DATA_WIDTH/8
) (
  input  logic                      user_clk,
  input  logic                      user_rst,

  // AXI-S RX
  input  logic [C_DATA_WIDTH-1:0]   m_axis_rx_tdata,
  input  logic                      m_axis_rx_tvalid,
  input  logic                      m_axis_rx_tready,
  input  logic                      m_axis_rx_tlast,   // not used but ok via .*
  input  logic [21:0]               m_axis_rx_tuser,

  // DUT outputs
  input  logic                      null_rx_tvalid,
  input  logic                      null_rx_tlast,
  input  logic [KEEP_WIDTH-1:0]     null_rx_tkeep,
  input  logic                      null_rdst_rdy,
  input  logic [4:0]                null_is_eof,

  // DUT internals
  input  logic                      cur_state,
  input  logic                      next_state,
  input  logic [11:0]               reg_pkt_len_counter,
  input  logic [11:0]               pkt_len_counter,
  input  logic [11:0]               pkt_len_counter_dec,
  input  logic                      pkt_done,
  input  logic [11:0]               new_pkt_len,
  input  logic                      straddle_sof,
  input  logic [KEEP_WIDTH-1:0]     eof_tkeep,
  input  logic                      eof
);

  localparam int unsigned INTERFACE_WIDTH_DWORDS = (C_DATA_WIDTH==128)?4:(C_DATA_WIDTH==64)?2:1;
  localparam logic IDLE=1'b0, IN_PACKET=1'b1;

  default clocking cb @ (posedge user_clk); endclocking
  default disable iff (user_rst);

  // Reset behavior
  assert property (user_rst |-> (cur_state==IDLE && reg_pkt_len_counter==12'h0));

  // Registered update correctness
  assert property (!user_rst |-> cur_state==$past(next_state));
  assert property (!user_rst |-> reg_pkt_len_counter==$past(pkt_len_counter));

  // State transition logic (combinational next_state)
  assert property (cur_state==IDLE &&  m_axis_rx_tvalid && m_axis_rx_tready && !eof |-> next_state==IN_PACKET);
  assert property (cur_state==IDLE && !(m_axis_rx_tvalid && m_axis_rx_tready && !eof) |-> next_state==IDLE);

  // Counter/state next-cycle behavior
  // IDLE: load new packet length
  assert property (cur_state==IDLE |=> reg_pkt_len_counter==$past(new_pkt_len));

  // IN_PACKET branches (mutually guarded)
  if (C_DATA_WIDTH==128) begin
    // straddle reload
    assert property (cur_state==IN_PACKET && straddle_sof && m_axis_rx_tvalid
                     |=> reg_pkt_len_counter==$past(new_pkt_len) && cur_state==IN_PACKET);
  end
  // done+ready -> go IDLE and reload
  assert property (cur_state==IN_PACKET
                   && !(C_DATA_WIDTH==128 && straddle_sof && m_axis_rx_tvalid)
                   && m_axis_rx_tready && pkt_done
                   |=> reg_pkt_len_counter==$past(new_pkt_len) && cur_state==IDLE);
  // decrement while not done
  assert property (cur_state==IN_PACKET
                   && !(C_DATA_WIDTH==128 && straddle_sof && m_axis_rx_tvalid)
                   && m_axis_rx_tready && !pkt_done
                   |=> reg_pkt_len_counter==$past(reg_pkt_len_counter)-INTERFACE_WIDTH_DWORDS && cur_state==IN_PACKET);
  // hold when !ready
  assert property (cur_state==IN_PACKET
                   && !(C_DATA_WIDTH==128 && straddle_sof && m_axis_rx_tvalid)
                   && !m_axis_rx_tready
                   |=> reg_pkt_len_counter==$past(reg_pkt_len_counter) && cur_state==IN_PACKET);

  // LAST / KEEP / READY relations
  assert property (null_rx_tlast == (reg_pkt_len_counter <= INTERFACE_WIDTH_DWORDS));
  assert property (null_rdst_rdy == null_rx_tlast);
  assert property (null_rx_tvalid); // constant 1
  assert property ( null_rx_tlast  |-> (null_rx_tkeep == eof_tkeep));
  assert property (!null_rx_tlast  |-> (null_rx_tkeep == {KEEP_WIDTH{1'b1}}));

  // straddle_sof and eof mapping checks
  if (C_DATA_WIDTH==128) begin
    assert property (straddle_sof == (m_axis_rx_tuser[14:13]==2'b11));
  end else begin
    assert property (!straddle_sof);
  end
  assert property (eof == m_axis_rx_tuser[21]);

  // eof_tkeep correctness per width
  if (C_DATA_WIDTH==128) begin
    assert property (eof_tkeep == {KEEP_WIDTH{1'b0}});
  end else if (C_DATA_WIDTH==64) begin
    assert property (eof_tkeep == { ((pkt_len_counter==12'd2)?4'hF:4'h0), 4'hF });
  end else begin // 32
    assert property (eof_tkeep == 4'hF);
  end

  // null_is_eof mapping per width
  if (C_DATA_WIDTH==128) begin
    assert property ((pkt_len_counter==12'd1) |-> (null_is_eof==5'b10011));
    assert property ((pkt_len_counter==12'd2) |-> (null_is_eof==5'b10111));
    assert property ((pkt_len_counter==12'd3) |-> (null_is_eof==5'b11011));
    assert property ((pkt_len_counter==12'd4) |-> (null_is_eof==5'b11111));
    assert property ((pkt_len_counter>=12'd5) |-> (null_is_eof==5'b00011));
  end else if (C_DATA_WIDTH==64) begin
    assert property ((pkt_len_counter==12'd1) |-> (null_is_eof==5'b10011));
    assert property ((pkt_len_counter==12'd2) |-> (null_is_eof==5'b10111));
    assert property ((pkt_len_counter>=12'd3) |-> (null_is_eof==5'b00011));
  end else begin
    assert property ((pkt_len_counter==12'd1) |-> (null_is_eof==5'b10011));
    assert property ((pkt_len_counter!=12'd1) |-> (null_is_eof==5'b00011));
  end

  // Coverage
  // Basic packet flow: IDLE -> IN_PACKET -> IDLE via done
  cover property (cur_state==IDLE && m_axis_rx_tvalid && m_axis_rx_tready && !eof
                  ##1 cur_state==IN_PACKET
                  ##[1:32] m_axis_rx_tready && pkt_done
                  ##1 cur_state==IDLE);

  // Decrement path observed
  cover property (cur_state==IN_PACKET && m_axis_rx_tready && !pkt_done
                  ##1 reg_pkt_len_counter==$past(reg_pkt_len_counter)-INTERFACE_WIDTH_DWORDS);

  // LAST toggle coverage
  cover property (!null_rx_tlast ##1 null_rx_tlast);
  cover property ( null_rx_tlast ##1 !null_rx_tlast);

  // Width-specific coverage
  if (C_DATA_WIDTH==128) begin
    cover property (cur_state==IN_PACKET && straddle_sof && m_axis_rx_tvalid);
    cover property (pkt_len_counter==12'd1 && null_rx_tlast);
    cover property (pkt_len_counter==12'd2 && null_rx_tlast);
    cover property (pkt_len_counter==12'd3 && null_rx_tlast);
    cover property (pkt_len_counter==12'd4 && null_rx_tlast);
  end else if (C_DATA_WIDTH==64) begin
    cover property (pkt_len_counter==12'd1 && null_rx_tlast);
    cover property (pkt_len_counter==12'd2 && null_rx_tlast);
  end else begin
    cover property (pkt_len_counter==12'd1 && null_rx_tlast);
  end

endmodule

// Bind into DUT (optional)
bind pcie_core_axi_basic_rx_null_gen
  pcie_core_axi_basic_rx_null_gen_sva #(
    .C_DATA_WIDTH(C_DATA_WIDTH),
    .KEEP_WIDTH  (KEEP_WIDTH)
  ) pcie_core_axi_basic_rx_null_gen_sva_i (.*);