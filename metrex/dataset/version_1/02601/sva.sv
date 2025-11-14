// SVA for pcie_rx_req
// Concise, high-signal-coverage, bindable assertions + covers

module pcie_rx_req_sva #(
  parameter int P_PCIE_DATA_WIDTH = 128,
  parameter int C_PCIE_ADDR_WIDTH = 36
) (pcie_rx_req dut);

  // Local copies of DUT state encodings/prefix used by SVA
  localparam [8:0] S_IDLE             = 9'b000000001;
  localparam [8:0] S_PCIE_RX_CMD_0    = 9'b000000010;
  localparam [8:0] S_PCIE_RX_CMD_1    = 9'b000000100;
  localparam [8:0] S_PCIE_CHK_NUM_MRD = 9'b000001000;
  localparam [8:0] S_PCIE_MRD_REQ     = 9'b000010000;
  localparam [8:0] S_PCIE_MRD_ACK     = 9'b000100000;
  localparam [8:0] S_PCIE_MRD_DONE    = 9'b001000000;
  localparam [8:0] S_PCIE_MRD_DELAY   = 9'b010000000;
  localparam [8:0] S_PCIE_MRD_NEXT    = 9'b100000000;

  localparam [3:0] LP_PCIE_TAG_PREFIX = 4'b0001;

  default clocking cb @(posedge dut.pcie_user_clk); endclocking
  default disable iff (!dut.pcie_user_rst_n)

  // Basic state sanity
  a_rst_idle:   assert property (!dut.pcie_user_rst_n |-> dut.cur_state == S_IDLE);
  a_onehot:     assert property ($onehot(dut.cur_state));

  // Precise next-state behavior
  a_idle_tr:    assert property ((dut.cur_state==S_IDLE && dut.pcie_rx_cmd_empty_n) |=> dut.cur_state==S_PCIE_RX_CMD_0);
  a_idle_hold:  assert property ((dut.cur_state==S_IDLE && !dut.pcie_rx_cmd_empty_n) |=> dut.cur_state==S_IDLE);
  a_rx0_tr:     assert property (dut.cur_state==S_PCIE_RX_CMD_0 |=> dut.cur_state==S_PCIE_RX_CMD_1);
  a_rx1_tr:     assert property (dut.cur_state==S_PCIE_RX_CMD_1 |=> dut.cur_state==S_PCIE_CHK_NUM_MRD);
  a_chk_hold:   assert property ((dut.cur_state==S_PCIE_CHK_NUM_MRD && !(dut.pcie_rx_fifo_full_n && dut.pcie_tag_full_n)) |=> dut.cur_state==S_PCIE_CHK_NUM_MRD);
  a_chk_go:     assert property ((dut.cur_state==S_PCIE_CHK_NUM_MRD && (dut.pcie_rx_fifo_full_n && dut.pcie_tag_full_n)) |=> dut.cur_state==S_PCIE_MRD_REQ);
  a_req_tr:     assert property (dut.cur_state==S_PCIE_MRD_REQ |=> dut.cur_state==S_PCIE_MRD_ACK);
  a_ack_hold:   assert property ((dut.cur_state==S_PCIE_MRD_ACK && !dut.tx_dma_mrd_req_ack) |=> dut.cur_state==S_PCIE_MRD_ACK);
  a_ack_go:     assert property ((dut.cur_state==S_PCIE_MRD_ACK && dut.tx_dma_mrd_req_ack) |=> dut.cur_state==S_PCIE_MRD_DONE);
  a_done_tr:    assert property (dut.cur_state==S_PCIE_MRD_DONE |=> dut.cur_state==S_PCIE_MRD_DELAY);
  a_delay_hold: assert property ((dut.cur_state==S_PCIE_MRD_DELAY && dut.r_pcie_mrd_delay!=0) |=> dut.cur_state==S_PCIE_MRD_DELAY);
  a_delay_go:   assert property ((dut.cur_state==S_PCIE_MRD_DELAY && dut.r_pcie_mrd_delay==0) |=> dut.cur_state==S_PCIE_MRD_NEXT);
  a_next_exit0: assert property ((dut.cur_state==S_PCIE_MRD_NEXT && dut.r_pcie_rx_len==0) |=> dut.cur_state==S_IDLE);
  a_next_more:  assert property ((dut.cur_state==S_PCIE_MRD_NEXT && dut.r_pcie_rx_len!=0) |=> dut.cur_state==S_PCIE_CHK_NUM_MRD);

  // Output control vs state (single-cycle exactness)
  a_rd_en_only_in_rx: assert property (dut.pcie_rx_cmd_rd_en == ((dut.cur_state==S_PCIE_RX_CMD_0) || (dut.cur_state==S_PCIE_RX_CMD_1)));
  a_tag_alloc_only_in_req: assert property (dut.pcie_tag_alloc == (dut.cur_state==S_PCIE_MRD_REQ));
  a_tx_req_only_in_req:    assert property (dut.tx_dma_mrd_req == (dut.cur_state==S_PCIE_MRD_REQ));

  // Req/alloc coherence and tag encoding
  a_tag_prefix_req:  assert property (dut.tx_dma_mrd_req |-> (dut.tx_dma_mrd_tag[7:4]==LP_PCIE_TAG_PREFIX));
  a_tag_prefix_alloc:assert property (dut.pcie_tag_alloc  |-> (dut.pcie_alloc_tag[7:4]==LP_PCIE_TAG_PREFIX));
  a_tag_match_on_req:assert property (dut.tx_dma_mrd_req |-> (dut.pcie_alloc_tag == dut.tx_dma_mrd_tag));
  a_len_consistency: assert property (dut.pcie_tag_alloc |-> (dut.pcie_tag_alloc_len == dut.tx_dma_mrd_len[9:4]));

  // Req only issued when resources were available in CHK (as per FSM gating)
  a_alloc_gated:     assert property (dut.pcie_tag_alloc |-> $past(dut.pcie_tag_full_n && dut.pcie_rx_fifo_full_n));

  // Stability of transaction fields from REQ through ACK wait
  a_hold_after_req:  assert property ($rose(dut.tx_dma_mrd_req) |-> (dut.tx_dma_mrd_tag == $past(dut.tx_dma_mrd_tag) &&
                                                                     dut.tx_dma_mrd_len == $past(dut.tx_dma_mrd_len) &&
                                                                     dut.tx_dma_mrd_addr== $past(dut.tx_dma_mrd_addr)));
  a_hold_in_ack_wait:assert property ((dut.cur_state==S_PCIE_MRD_ACK && !dut.tx_dma_mrd_req_ack) |->
                                      ($stable(dut.tx_dma_mrd_tag) && $stable(dut.tx_dma_mrd_len) && $stable(dut.tx_dma_mrd_addr)));

  // ACK effect
  a_ack_to_done_no_req: assert property ($rose(dut.tx_dma_mrd_req_ack) |-> (dut.cur_state==S_PCIE_MRD_DONE));

  // Tag monotonic increment across allocations (low nibble wraps)
  logic [3:0] last_alloc_tag;
  always @(posedge dut.pcie_user_clk) if (dut.pcie_user_rst_n && dut.pcie_tag_alloc) last_alloc_tag <= dut.pcie_alloc_tag[3:0];
  a_tag_inc: assert property (dut.pcie_tag_alloc ##[1:$] dut.pcie_tag_alloc |-> (dut.pcie_alloc_tag[3:0] == last_alloc_tag + 4'd1));

  // Structural no-X when valid
  a_no_x_req_bus:    assert property (dut.tx_dma_mrd_req |-> !$isunknown({dut.tx_dma_mrd_tag,dut.tx_dma_mrd_len,dut.tx_dma_mrd_addr})));
  a_no_x_alloc_bus:  assert property (dut.pcie_tag_alloc  |-> !$isunknown({dut.pcie_alloc_tag,dut.pcie_tag_alloc_len})));

  // Coverage
  c_full_path_one_read: cover property (
    dut.cur_state==S_IDLE && dut.pcie_rx_cmd_empty_n ##1
    dut.cur_state==S_PCIE_RX_CMD_0 ##1
    dut.cur_state==S_PCIE_RX_CMD_1 ##1
    dut.cur_state==S_PCIE_CHK_NUM_MRD ##1
    dut.cur_state==S_PCIE_MRD_REQ ##1
    dut.cur_state==S_PCIE_MRD_ACK ##[1:$] dut.tx_dma_mrd_req_ack ##1
    dut.cur_state==S_PCIE_MRD_DONE ##1
    dut.cur_state==S_PCIE_MRD_DELAY ##[1:$]
    dut.cur_state==S_PCIE_MRD_NEXT ##1
    dut.cur_state==S_IDLE
  );

  c_multi_mrd: cover property (dut.cur_state==S_PCIE_MRD_NEXT && dut.r_pcie_rx_len!=0 ##1 dut.cur_state==S_PCIE_CHK_NUM_MRD);

endmodule

// Bind into the DUT
bind pcie_rx_req pcie_rx_req_sva #(.P_PCIE_DATA_WIDTH(P_PCIE_DATA_WIDTH),
                                   .C_PCIE_ADDR_WIDTH(C_PCIE_ADDR_WIDTH)) pcie_rx_req_sva_i(.dut(this));