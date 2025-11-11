// SVA for axi_basic_rx_null_gen
`ifndef AXI_BASIC_RX_NULL_GEN_SVA
`define AXI_BASIC_RX_NULL_GEN_SVA

bind axi_basic_rx_null_gen axi_basic_rx_null_gen_sva();

module axi_basic_rx_null_gen_sva;

  default clocking cb @(posedge user_clk); endclocking
  default disable iff (user_rst);

  // Reset behavior (checked even when reset is high)
  assert property (@(posedge user_clk) user_rst |-> (cur_state==IDLE && reg_pkt_len_counter==12'h0));

  // FSM next-state checks
  assert property (cur_state==IDLE && m_axis_rx_tvalid && m_axis_rx_tready && !eof |=> cur_state==IN_PACKET);
  assert property (cur_state==IDLE && !(m_axis_rx_tvalid && m_axis_rx_tready && !eof) |=> cur_state==IDLE);

  generate if (C_DATA_WIDTH==128) begin
    // straddle takes priority and stays IN_PACKET
    assert property (cur_state==IN_PACKET && m_axis_rx_tvalid && straddle_sof |=> cur_state==IN_PACKET);
  end endgenerate

  // Done->IDLE (unless straddle branch took priority)
  assert property (cur_state==IN_PACKET && m_axis_rx_tready && pkt_done &&
                   !(C_DATA_WIDTH==128 && m_axis_rx_tvalid && straddle_sof)
                   |=> cur_state==IDLE);

  // Otherwise remain IN_PACKET
  assert property (cur_state==IN_PACKET &&
                   !((C_DATA_WIDTH==128 && m_axis_rx_tvalid && straddle_sof) || (m_axis_rx_tready && pkt_done))
                   |=> cur_state==IN_PACKET);

  // Counter update checks
  assert property (cur_state==IDLE |=> reg_pkt_len_counter == new_pkt_len);

  generate if (C_DATA_WIDTH==128) begin
    assert property (cur_state==IN_PACKET && m_axis_rx_tvalid && straddle_sof
                     |=> reg_pkt_len_counter == new_pkt_len);
  end endgenerate

  assert property (cur_state==IN_PACKET && m_axis_rx_tready && pkt_done &&
                   !(C_DATA_WIDTH==128 && m_axis_rx_tvalid && straddle_sof)
                   |=> reg_pkt_len_counter == new_pkt_len);

  assert property (cur_state==IN_PACKET && m_axis_rx_tready && !pkt_done &&
                   !(C_DATA_WIDTH==128 && m_axis_rx_tvalid && straddle_sof)
                   |=> reg_pkt_len_counter == $past(reg_pkt_len_counter,1,user_rst) - INTERFACE_WIDTH_DWORDS);

  assert property (cur_state==IN_PACKET && !m_axis_rx_tready &&
                   !(C_DATA_WIDTH==128 && m_axis_rx_tvalid && straddle_sof)
                   |=> reg_pkt_len_counter == $past(reg_pkt_len_counter,1,user_rst));

  // Output invariants
  assert property (null_rx_tvalid);
  assert property (null_rx_tlast == (pkt_len_counter <= INTERFACE_WIDTH_DWORDS));
  assert property (null_rdst_rdy == null_rx_tlast);
  assert property (!null_rx_tlast |-> null_rx_tkeep == {KEEP_WIDTH{1'b1}});
  assert property (null_rx_tlast  |-> null_rx_tkeep == eof_tkeep);

  // Encoding/decoding checks
  // straddle decode
  generate
    if (C_DATA_WIDTH==128) begin
      assert property (straddle_sof == (m_axis_rx_tuser[14:13]==2'b11));
    end else begin
      assert property (!straddle_sof);
    end
  endgenerate

  // eof_tkeep and null_is_eof encodings
  generate
    if (C_DATA_WIDTH==128) begin
      assert property (eof_tkeep == {KEEP_WIDTH{1'b0}});
      assert property (pkt_len_counter==12'd1 |-> null_is_eof==5'b10011);
      assert property (pkt_len_counter==12'd2 |-> null_is_eof==5'b10111);
      assert property (pkt_len_counter==12'd3 |-> null_is_eof==5'b11011);
      assert property (pkt_len_counter==12'd4 |-> null_is_eof==5'b11111);
      assert property (!(pkt_len_counter inside {12'd1,12'd2,12'd3,12'd4}) |-> null_is_eof==5'b00011);
    end else if (C_DATA_WIDTH==64) begin
      assert property (eof_tkeep == { ((pkt_len_counter==12'd2)?4'hF:4'h0), 4'hF });
      assert property (pkt_len_counter==12'd1 |-> null_is_eof==5'b10011);
      assert property (pkt_len_counter==12'd2 |-> null_is_eof==5'b10111);
      assert property (!(pkt_len_counter inside {12'd1,12'd2}) |-> null_is_eof==5'b00011);
    end else begin // 32-bit
      assert property (eof_tkeep == {KEEP_WIDTH{1'b1}});
      assert property (pkt_len_counter==12'd1 |-> null_is_eof==5'b10011);
      assert property (pkt_len_counter!=12'd1 |-> null_is_eof==5'b00011);
    end
  endgenerate

  // Payload length gating
  assert property (!packet_fmt[1] |-> payload_len==10'h0);

  // Sanity: state encoding
  assert property (cur_state inside {IDLE, IN_PACKET});

  // Coverage
  cover property (cur_state==IDLE ##1 m_axis_rx_tvalid && m_axis_rx_tready && !eof ##1 cur_state==IN_PACKET);
  cover property (cur_state==IN_PACKET && m_axis_rx_tready && !pkt_done);
  cover property (cur_state==IN_PACKET && m_axis_rx_tready && pkt_done ##1 cur_state==IDLE);
  generate
    if (C_DATA_WIDTH==128) begin
      cover property (cur_state==IN_PACKET && m_axis_rx_tvalid && straddle_sof);
      cover property (pkt_len_counter inside {12'd1,12'd2,12'd3,12'd4});
    end else if (C_DATA_WIDTH==64) begin
      cover property (null_rx_tlast && (pkt_len_counter==12'd2));
      cover property (null_rx_tlast && (pkt_len_counter!=12'd2));
    end else begin
      cover property (null_rx_tlast);
    end
  endgenerate

endmodule

`endif