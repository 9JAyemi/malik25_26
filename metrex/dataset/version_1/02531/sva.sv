// Add this SVA block inside the module (e.g., near the end). It is parameter- and generate-aware.
// Wrap with ASSERT_ON to enable in sim/formal.

`ifdef ASSERT_ON
  // Default clocking and reset gating
  default clocking cb @(posedge user_clk); endclocking
  default disable iff (user_rst);

  // Basic equivalences and mapping checks
  assert property (trn_teof == reg_tlast);
  assert property (trn_tecrc_gen == reg_tuser[0]);
  assert property (trn_terrfwd   == reg_tuser[1]);
  assert property (trn_tstr      == reg_tuser[2]);
  assert property (trn_tsrc_dsc  == reg_tuser[3]);
  assert property (trn_tsof == (reg_tvalid && !trn_in_packet));

  // In-packet state machine consistency
  assert property ((trn_tsof && trn_tsrc_rdy && trn_tdst_rdy && !trn_teof) |=> trn_in_packet);
  assert property ((trn_in_packet && trn_teof && trn_tsrc_rdy) |=> !trn_in_packet);
  assert property ((!trn_lnk_up) |=> !trn_in_packet);
  assert property (trn_in_packet |-> !trn_tsof);

  // TRN interface stability under backpressure
  assert property ((trn_tsrc_rdy && !trn_tdst_rdy) |-> $stable({trn_td, trn_trem, trn_tsof, trn_teof, trn_terrfwd, trn_tstr, trn_tecrc_gen, trn_tsrc_dsc}));

  // AXI packet tracker and flush
  assert property ((axi_beat_live && !s_axis_tx_tlast) |=> axi_in_packet);
  assert property (axi_beat_live |=> (axi_in_packet == !s_axis_tx_tlast));
  assert property ((axi_in_packet && !trn_lnk_up && !axi_end_packet) |=> flush_axi);
  assert property (axi_end_packet |=> !flush_axi);

  // trem and data swap mapping by data width
  generate
    if (C_DATA_WIDTH == 128) begin
      assert property (trn_td == {reg_tdata[31:0], reg_tdata[63:32], reg_tdata[95:64], reg_tdata[127:96]});
      assert property (trn_trem[1] == reg_tkeep[11]);
      assert property (trn_trem[0] == (reg_tkeep[15] || (reg_tkeep[7] && !reg_tkeep[11])));
    end
    else if (C_DATA_WIDTH == 64) begin
      assert property (trn_td == {reg_tdata[31:0], reg_tdata[63:32]});
      assert property (trn_trem == reg_tkeep[7]);
    end
    else begin
      assert property (trn_td == reg_tdata);
      assert property (trn_trem == 1'b0);
    end
  endgenerate

  // Configuration-specific checks
  generate
    if (C_PM_PRIORITY == "FALSE") begin : sva_throttle_ctl_pipeline
      // Registered pass-through of AXI to internal regs (1-cycle)
      assert property ({reg_tdata, reg_tvalid, reg_tkeep, reg_tlast, reg_tuser} == $past({s_axis_tx_tdata, s_axis_tx_tvalid, s_axis_tx_tkeep, s_axis_tx_tlast, s_axis_tx_tuser}));
      // trn_tsrc_rdy registered from axi_beat_live and gating
      assert property (trn_tsrc_rdy == $past(axi_beat_live && !disable_trn));
      // tready mapping
      assert property (s_axis_tx_tready == tready_thrtl);
      // disable_trn composition
      assert property (disable_trn == (reg_disable_trn || !trn_lnk_up));
      // reg_disable_trn state transitions
      assert property ((axi_in_packet && !trn_lnk_up && !axi_end_packet) |=> reg_disable_trn);
      assert property (axi_end_packet |=> !reg_disable_trn);
    end
    else begin : sva_pm_prioity_pipeline
      // When holding data (src_rdy && !dst_rdy), internal regs must be stable
      assert property ((trn_tsrc_rdy && !trn_tdst_rdy) |-> $stable({reg_tdata, reg_tvalid, reg_tkeep, reg_tlast, reg_tuser}));

      // Prev-stage holding behavior
      assert property (!s_axis_tx_tready |-> $stable({tdata_prev, tvalid_prev, tkeep_prev, tlast_prev, tuser_prev}));
      assert property (s_axis_tx_tready |=> {tdata_prev, tvalid_prev, tkeep_prev, tlast_prev, tuser_prev} == $past({s_axis_tx_tdata, s_axis_tx_tvalid, s_axis_tx_tkeep, s_axis_tx_tlast, s_axis_tx_tuser}));

      // Load path selection into reg_* when not holding
      assert property ((!data_hold && !data_prev) |-> {reg_tdata, reg_tvalid, reg_tkeep, reg_tlast, reg_tuser} == $past({s_axis_tx_tdata, s_axis_tx_tvalid, s_axis_tx_tkeep, s_axis_tx_tlast, s_axis_tx_tuser}));
      assert property ((!data_hold &&  data_prev) |-> {reg_tdata, reg_tvalid, reg_tkeep, reg_tlast, reg_tuser} == $past({tdata_prev,      tvalid_prev,      tkeep_prev,      tlast_prev,      tuser_prev}));

      // tsrc_rdy gating and tready behavior
      assert property (trn_tsrc_rdy == (reg_tvalid && !disable_trn));
      assert property ((flush_axi && !axi_end_packet) |=> s_axis_tx_tready);
      assert property ((!flush_axi && trn_lnk_up)     |=> s_axis_tx_tready == (trn_tdst_rdy || !trn_tsrc_rdy));
      assert property ((!flush_axi && !trn_lnk_up)    |=> !s_axis_tx_tready);

      // disable_trn transitions and mapping
      assert property (disable_trn == reg_disable_trn);
      assert property ((!trn_lnk_up) |=> disable_trn);
      assert property ((!flush_axi && s_axis_tx_tready && trn_lnk_up) |=> !disable_trn);
    end
  endgenerate

  // Reset effects on local state
  assert property (user_rst |-> (!trn_in_packet && !axi_in_packet));

  // Coverage: representative scenarios
  cover property (trn_tsof && trn_tsrc_rdy && trn_tdst_rdy ##1 trn_in_packet ##[1:10] trn_teof && trn_tsrc_rdy);
  cover property (axi_beat_live && !s_axis_tx_tlast ##1 axi_in_packet ##1 !trn_lnk_up ##1 flush_axi ##[1:10] axi_end_packet ##1 !flush_axi);
  cover property (trn_tsrc_rdy && !trn_tdst_rdy ##[1:5] trn_tsrc_rdy && trn_tdst_rdy);
  cover property (disable_trn ##[1:20] !disable_trn);

  generate
    if (C_DATA_WIDTH == 128) begin
      cover property (trn_teof && trn_trem == 2'b00);
      cover property (trn_teof && trn_trem == 2'b01);
      cover property (trn_teof && trn_trem == 2'b10);
      cover property (trn_teof && trn_trem == 2'b11);
    end
    else if (C_DATA_WIDTH == 64) begin
      cover property (trn_teof && trn_trem == 1'b0);
      cover property (trn_teof && trn_trem == 1'b1);
    end
  endgenerate
`endif // ASSERT_ON