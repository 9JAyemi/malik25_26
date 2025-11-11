// SVA for axi_basic_tx_pipeline
// Bind into the DUT so we can reference internal signals
bind axi_basic_tx_pipeline axi_basic_tx_pipeline_sva #(
  .C_DATA_WIDTH (C_DATA_WIDTH),
  .C_PM_PRIORITY(C_PM_PRIORITY),
  .REM_WIDTH    (REM_WIDTH),
  .STRB_WIDTH   (STRB_WIDTH)
) i_axi_basic_tx_pipeline_sva();

module axi_basic_tx_pipeline_sva #(
  parameter int C_DATA_WIDTH = 128,
  parameter string C_PM_PRIORITY = "FALSE",
  parameter int REM_WIDTH = (C_DATA_WIDTH == 128) ? 2 : 1,
  parameter int STRB_WIDTH = C_DATA_WIDTH/8
) ();

  default clocking cb @(posedge user_clk); endclocking
  default disable iff (user_rst);

  // Basic derived wires correctness
  assert property (axi_beat_live == (s_axis_tx_tvalid && s_axis_tx_tready));
  assert property (axi_end_packet == (s_axis_tx_tvalid && s_axis_tx_tready && s_axis_tx_tlast));

  // AXI-Stream input protocol: hold data/control while valid && !ready
  assert property (s_axis_tx_tvalid && !s_axis_tx_tready |->
                   $stable({s_axis_tx_tdata,s_axis_tx_tstrb,s_axis_tx_tlast,s_axis_tx_tuser}) throughout (!s_axis_tx_tready));

  // tuser and tlast mappings
  assert property (trn_teof      == reg_tlast);
  assert property (trn_tecrc_gen == reg_tuser[0]);
  assert property (trn_terrfwd   == reg_tuser[1]);
  assert property (trn_tstr      == reg_tuser[2]);
  assert property (trn_tsrc_dsc  == reg_tuser[3]);

  // trn_td endianness swap per width
  generate
    if (C_DATA_WIDTH == 128) begin
      assert property (trn_td[127:96] == reg_tdata[ 31:  0]
                    && trn_td[ 95:64] == reg_tdata[ 63: 32]
                    && trn_td[ 63:32] == reg_tdata[ 95: 64]
                    && trn_td[ 31: 0] == reg_tdata[127: 96]);
    end else if (C_DATA_WIDTH == 64) begin
      assert property (trn_td[63:32] == reg_tdata[31: 0]
                    && trn_td[31: 0] == reg_tdata[63:32]);
    end else begin
      assert property (trn_td == reg_tdata);
    end
  endgenerate

  // tstrb to trem mapping
  generate
    if (C_DATA_WIDTH == 128) begin
      assert property (trn_trem[1] == reg_tstrb[11]);
      assert property (trn_trem[0] == (reg_tstrb[15] || (reg_tstrb[7] && !reg_tstrb[11])));
    end else if (C_DATA_WIDTH == 64) begin
      assert property (trn_trem == reg_tstrb[7]);
    end else begin
      assert property (trn_trem == '0);
    end
  endgenerate

  // Start-of-frame generation
  assert property (trn_tsof == (reg_tvalid && !trn_in_packet));
  assert property (trn_in_packet |-> !trn_tsof);

  // trn_in_packet state machine
  assert property (trn_tsof && trn_tsrc_rdy && trn_tdst_rdy && !trn_teof |=> trn_in_packet);
  assert property (trn_in_packet && trn_teof && trn_tsrc_rdy |=> !trn_in_packet);
  assert property (!trn_lnk_up |=> !trn_in_packet);

  // axi_in_packet state machine
  assert property (axi_beat_live && !s_axis_tx_tlast |=> axi_in_packet);
  assert property (axi_beat_live &&  s_axis_tx_tlast |=> !axi_in_packet);

  // Flush state
  assert property (axi_in_packet && !trn_lnk_up && !axi_end_packet |=> flush_axi);
  assert property (axi_end_packet |=> !flush_axi);

  // Mode-dependent assertions
  generate
    if (C_PM_PRIORITY == "FALSE") begin : SVA_THROTTLE
      // s_axis ready passthrough
      assert property (s_axis_tx_tready == tready_thrtl);

      // Registered source-ready equals past(axi_beat_live && !disable_trn)
      assert property (trn_tsrc_rdy == reg_tsrc_rdy);
      assert property (reg_tsrc_rdy == $past(axi_beat_live && !disable_trn));

      // Pipeline captures AXI inputs each cycle
      assert property (reg_tdata  == $past(s_axis_tx_tdata));
      assert property (reg_tvalid == $past(s_axis_tx_tvalid));
      assert property (reg_tstrb  == $past(s_axis_tx_tstrb));
      assert property (reg_tlast  == $past(s_axis_tx_tlast));
      assert property (reg_tuser  == $past(s_axis_tx_tuser));

      // disable_trn combination
      assert property (disable_trn == (reg_disable_trn || !trn_lnk_up));

      // reg_disable_trn FSM
      assert property (axi_in_packet && !trn_lnk_up && !axi_end_packet |=> reg_disable_trn);
      assert property (axi_end_packet |=> !reg_disable_trn);
    end else begin : SVA_PM
      // s_axis ready driven by reg_tready
      assert property (s_axis_tx_tready == reg_tready);

      // trn_tsrc_rdy gating
      assert property (trn_tsrc_rdy == (reg_tvalid && !disable_trn));

      // data_hold and data_prev behavior
      assert property (data_hold |=> $stable({reg_tdata,reg_tvalid,reg_tstrb,reg_tlast,reg_tuser}));
      assert property (data_prev == $past(data_hold));

      // Data mux on load cycles
      assert property (!pm_prioity_pipeline.data_hold && pm_prioity_pipeline.data_prev |=> 
                       reg_tdata  == $past(pm_prioity_pipeline.tdata_prev)  &&
                       reg_tvalid == $past(pm_prioity_pipeline.tvalid_prev) &&
                       reg_tstrb  == $past(pm_prioity_pipeline.tstrb_prev)  &&
                       reg_tlast  == $past(pm_prioity_pipeline.tlast_prev)  &&
                       reg_tuser  == $past(pm_prioity_pipeline.tuser_prev));

      assert property (!pm_prioity_pipeline.data_hold && !pm_prioity_pipeline.data_prev |=> 
                       reg_tdata  == $past(s_axis_tx_tdata)  &&
                       reg_tvalid == $past(s_axis_tx_tvalid) &&
                       reg_tstrb  == $past(s_axis_tx_tstrb)  &&
                       reg_tlast  == $past(s_axis_tx_tlast)  &&
                       reg_tuser  == $past(s_axis_tx_tuser));

      // reg_tready next-state function
      assert property (reg_tready == $past( (flush_axi && !axi_end_packet) ? 1'b1
                                            : (trn_lnk_up ? (trn_tdst_rdy || !trn_tsrc_rdy) : 1'b0) ));

      // disable_trn = reg_disable_trn
      assert property (disable_trn == reg_disable_trn);

      // reg_disable_trn behavior
      assert property (!trn_lnk_up |=> reg_disable_trn);
      assert property (!flush_axi && s_axis_tx_tready |=> !reg_disable_trn);
    end
  endgenerate

  // Key coverage
  cover property (trn_tsof && trn_tsrc_rdy && trn_tdst_rdy);
  cover property (trn_teof && trn_tsrc_rdy && trn_tdst_rdy);
  cover property (trn_tsof && trn_teof && trn_tsrc_rdy && trn_tdst_rdy);
  cover property (axi_in_packet && !trn_lnk_up && !axi_end_packet ##1 flush_axi);
  cover property (trn_tsrc_rdy && !trn_tdst_rdy ##1 trn_tsrc_rdy && trn_tdst_rdy);
  cover property (!trn_lnk_up ##1 trn_lnk_up);

endmodule