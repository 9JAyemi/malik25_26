// SVA for aurora_64b66b_25p4G_RX_LL_DATAPATH
module aurora_64b66b_25p4G_RX_LL_DATAPATH_sva;

  // Default sampling/disable
  default clocking cb @(posedge USER_CLK); endclocking
  default disable iff (RESET);

  // Helpers
  function automatic [7:0] nb2keep (input [2:0] nb);
    case (nb)
      3'd0: nb2keep = 8'hFF;
      3'd1: nb2keep = 8'h80;
      3'd2: nb2keep = 8'hC0;
      3'd3: nb2keep = 8'hE0;
      3'd4: nb2keep = 8'hF0;
      3'd5: nb2keep = 8'hF8;
      3'd6: nb2keep = 8'hFC;
      3'd7: nb2keep = 8'hFE;
      default: nb2keep = 8'h00;
    endcase
  endfunction

  // Pipeline correctness
  assert property (!pipe1_rx_pdu_in_progress_c |-> $stable(raw_data_r));
  assert property ( pipe1_rx_pdu_in_progress_c |=> raw_data_r == $past(raw_data_c));
  assert property ( raw_data_r2 == $past(raw_data_r));

  // Control invariants
  assert property (rx_pdu_ok == (rx_pe_data_v_r | (rx_pe_data_v_r & ((pipe1_rx_sep_r & !pipe1_rx_keep[STRB_WIDTH-1]) | pipe1_rx_sep7_r))));
  assert property (rx_tvalid_c == (rx_pdu_ok | dv_conic_sep | sep0_detect));

  // m_axi_rx_tvalid behavior
  assert property (!CHANNEL_UP |=> m_axi_rx_tvalid == 1'b0);
  assert property ( CHANNEL_UP &&  sep_conic_dv |=> m_axi_rx_tvalid == 1'b0);
  assert property ( CHANNEL_UP && !sep_conic_dv |=> m_axi_rx_tvalid == $past(rx_tvalid_c));

  // m_axi_rx_tdata update on valid
  assert property (rx_tvalid_c |=> m_axi_rx_tdata == $past(pipe2_rx_pe_data_r));

  // m_axi_rx_tkeep priority mux
  assert property ( sep_detect                 |=> m_axi_rx_tkeep == $past(rx_txkeep_c_1));
  assert property (!sep_detect &&  sep0_detect |=> m_axi_rx_tkeep == $past(rx_txkeep_c));
  assert property (!sep_detect && !sep0_detect |=> m_axi_rx_tkeep == 8'hFF);

  // m_axi_rx_tlast generation
  assert property (!CHANNEL_UP |=> m_axi_rx_tlast == 1'b0);
  assert property ( CHANNEL_UP |=> m_axi_rx_tlast == ($past(rx_tvalid_c) ? $past(sep_detect | sep0_detect) : 1'b0));

  // hold_valid_r sequencing
  assert property (!CHANNEL_UP |=> hold_valid_r == 1'b0);
  assert property ( CHANNEL_UP  |=> hold_valid_r == $past(hold_valid));

  // RX keep decode (combinational policy)
  assert property ( (RX_SEP || RX_SEP7) |-> rx_keep_dec_lane_0 == nb2keep(RX_SEP_NB));
  assert property ( !(RX_SEP || RX_SEP7) &&  RX_PE_DATA_V |-> rx_keep_dec_lane_0 == 8'hFF);
  assert property ( !(RX_SEP || RX_SEP7) && !RX_PE_DATA_V |-> rx_keep_dec_lane_0 == 8'h00);

  // Coverage
  cover property ($rose(m_axi_rx_tvalid));
  cover property (m_axi_rx_tvalid && m_axi_rx_tlast);
  cover property (sep_detect);
  cover property (sep0_detect);
  cover property (dv_conic_sep);
  cover property (sep_conic_dv);
  cover property (pipe1_rx_pdu_in_progress_c);
  cover property ((RX_SEP || RX_SEP7) && RX_SEP_NB==3'd0 && rx_keep_dec_lane_0==8'hFF);
  cover property ((RX_SEP || RX_SEP7) && RX_SEP_NB==3'd4 && rx_keep_dec_lane_0==8'hF0);
  cover property ((RX_SEP || RX_SEP7) && RX_SEP_NB==3'd7 && rx_keep_dec_lane_0==8'hFE);
  cover property (! (RX_SEP || RX_SEP7) && RX_PE_DATA_V && rx_keep_dec_lane_0==8'hFF);
  cover property (CHANNEL_UP && $rose(hold_valid_r));
  cover property (CHANNEL_UP && $fell(hold_valid_r));
  cover property (m_axi_rx_tlast && (m_axi_rx_tkeep==rx_txkeep_c_1)); // sep_detect path
  cover property (m_axi_rx_tlast && (m_axi_rx_tkeep==rx_txkeep_c));   // sep0_detect path

endmodule

bind aurora_64b66b_25p4G_RX_LL_DATAPATH aurora_64b66b_25p4G_RX_LL_DATAPATH_sva sva_inst();