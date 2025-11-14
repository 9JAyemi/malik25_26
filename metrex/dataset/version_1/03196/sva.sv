// SVA for axi_protocol_converter_v2_1_7_w_axi3_conv
module axi_protocol_converter_v2_1_7_w_axi3_conv_sva;
  default clocking cb @(posedge ACLK); endclocking
  default disable iff (ARESET);

  // Reset state
  a_reset_state: assert property (ARESET |=> (first_mi_word && (length_counter_1==8'd0)));

  // Interface relations
  a_wvalid_eq:   assert property (M_AXI_WVALID == (S_AXI_WVALID && cmd_valid));
  a_wready_eq:   assert property (S_AXI_WREADY == (S_AXI_WVALID && cmd_valid && M_AXI_WREADY));
  a_pop_eq:      assert property (pop_mi_data == (M_AXI_WVALID && M_AXI_WREADY));
  a_stall_eq:    assert property (mi_stalling == (M_AXI_WVALID && !M_AXI_WREADY));
  a_cmdr_eq:     assert property (cmd_ready == (cmd_valid && M_AXI_WVALID && M_AXI_WREADY && last_word));
  a_wlast_map:   assert property (M_AXI_WLAST == last_word);
  a_ready_tie:   assert property (M_AXI_WREADY_I == M_AXI_WREADY);

  // Counter/last logic
  a_len_sel_first:  assert property (first_mi_word  -> (length_counter[3:0]==cmd_length && length_counter[7:4]==4'd0));
  a_len_sel_next:   assert property (!first_mi_word -> (length_counter == length_counter_1));
  a_next_dec:       assert property (next_length_counter == (length_counter - 8'd1));
  a_len_update:     assert property (pop_mi_data |=> (length_counter_1 == $past(next_length_counter)));
  a_first_after_last: assert property (pop_mi_data && M_AXI_WLAST |=> first_mi_word);
  a_first_mid_burst:  assert property (pop_mi_data && !M_AXI_WLAST |=> !first_mi_word);

  // Burst/no-burst
  g_burst: if (C_SUPPORT_BURSTS!=0) begin
    a_last_word_def: assert property (last_word == last_beat);
    a_last_beat_def: assert property (last_beat == (length_counter==8'd0));
  end else begin
    a_noburst_last:  assert property (M_AXI_WLAST && last_word);
  end

  // Pass-through and AXI master-side stability
  a_id_passthru:    assert property (M_AXI_WVALID |-> (M_AXI_WID==cmd_id));
  a_data_passthru:  assert property (M_AXI_WVALID |-> (M_AXI_WDATA==S_AXI_WDATA));
  a_strb_passthru:  assert property (M_AXI_WVALID |-> (M_AXI_WSTRB==S_AXI_WSTRB));
  g_user: if (C_AXI_SUPPORTS_USER_SIGNALS!=0) begin
    a_user_passthru: assert property (M_AXI_WVALID |-> (M_AXI_WUSER==S_AXI_WUSER));
  end else begin
    a_user_zero:     assert property (M_AXI_WUSER=={C_AXI_WUSER_WIDTH{1'b0}});
  end
  a_hold_when_stall: assert property (M_AXI_WVALID && !M_AXI_WREADY |=> $stable({M_AXI_WVALID,M_AXI_WDATA,M_AXI_WSTRB,M_AXI_WUSER,M_AXI_WID,M_AXI_WLAST}));

  // Sanity when cmd invalid
  a_idle_when_no_cmd: assert property (!cmd_valid -> (!M_AXI_WVALID && !S_AXI_WREADY && !cmd_ready));

  // No X on outputs when valid
  a_no_x_m_core: assert property (M_AXI_WVALID |-> !$isunknown({M_AXI_WDATA,M_AXI_WSTRB,M_AXI_WID,M_AXI_WLAST}));
  g_user_x: if (C_AXI_SUPPORTS_USER_SIGNALS!=0) begin
    a_no_x_user: assert property (M_AXI_WVALID |-> !$isunknown(M_AXI_WUSER));
  end

  // Environment assumptions (for robustness)
  as_w_hold_on_stall: assume property (S_AXI_WVALID && !S_AXI_WREADY |=> S_AXI_WVALID && $stable({S_AXI_WDATA,S_AXI_WSTRB})); 
  g_assume_user: if (C_AXI_SUPPORTS_USER_SIGNALS!=0) begin
    as_wuser_hold: assume property (S_AXI_WVALID && !S_AXI_WREADY |=> $stable(S_AXI_WUSER));
  end
  as_cmd_hold: assume property (cmd_valid && !cmd_ready |=> cmd_valid && $stable({cmd_id,cmd_length}));

  // Coverage
  c_single_beat: cover property (cmd_valid && S_AXI_WVALID && M_AXI_WREADY && first_mi_word && (length_counter==8'd0) ##1 cmd_ready);
  c_multi_beat:  cover property (cmd_valid && S_AXI_WVALID && M_AXI_WREADY && first_mi_word && (length_counter!=8'd0)
                                 ##[1:$] M_AXI_WVALID && M_AXI_WREADY && M_AXI_WLAST ##1 cmd_ready);
  c_stall_then_go: cover property (M_AXI_WVALID && !M_AXI_WREADY ##1 M_AXI_WVALID && M_AXI_WREADY);
  c_user_cov: if (C_AXI_SUPPORTS_USER_SIGNALS!=0) cover property (M_AXI_WVALID && M_AXI_WREADY && (M_AXI_WUSER!=0));
  c_noburst_cov: if (C_SUPPORT_BURSTS==0) cover property (M_AXI_WVALID && M_AXI_WREADY && M_AXI_WLAST);
endmodule

bind axi_protocol_converter_v2_1_7_w_axi3_conv axi_protocol_converter_v2_1_7_w_axi3_conv_sva();