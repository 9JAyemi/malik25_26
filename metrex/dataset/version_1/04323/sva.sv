// SVA for axi_axis_writer
// Bind into all instances of DUT
bind axi_axis_writer axi_axis_writer_sva();

module axi_axis_writer_sva;

  default clocking cb @(posedge aclk); endclocking
  default disable iff (!aresetn);

  // Reset values
  assert property (!aresetn |-> (int_awready_reg && int_wready_reg && !int_bvalid_reg && int_wdata_reg == '0));

  // Registered next-state checks
  assert property ($past(aresetn) |-> int_awready_reg == $past(int_awready_next));
  assert property ($past(aresetn) |-> int_wready_reg  == $past(int_wready_next));
  assert property ($past(aresetn) |-> int_bvalid_reg  == $past(int_bvalid_next));
  assert property ($past(aresetn) |-> int_wdata_reg   == $past(int_wdata_next));

  // Output constants
  assert property (s_axi_bresp  == 2'd0);
  assert property (s_axi_arready== 1'b0);
  assert property (s_axi_rvalid == 1'b0);
  assert property (s_axi_rdata  == {(AXI_DATA_WIDTH){1'b0}});
  assert property (s_axi_rresp  == 2'd0);

  // No X on key outputs
  assert property (!$isunknown({s_axi_awready, s_axi_wready, s_axi_bresp, s_axi_bvalid,
                                s_axi_arready, s_axi_rdata, s_axi_rresp, s_axi_rvalid,
                                m_axis_tdata, m_axis_tvalid}));

  // Data path
  assert property (m_axis_tdata == (int_wready_reg ? s_axi_wdata : int_wdata_reg));
  assert property (int_wready_reg |=> int_wdata_reg == $past(s_axi_wdata));
  assert property (!int_wready_reg |=> $stable(int_wdata_reg));

  // TVALID relation
  assert property (m_axis_tvalid == (int_awdone_wire && int_wdone_wire && int_bdone_wire));

  // AWREADY behavior: drops after capture, stays low until W and B are done
  assert property ((s_axi_awready && s_axi_awvalid && !(int_wdone_wire && int_bdone_wire)) |=> !s_axi_awready);
  assert property ((s_axi_awready && s_axi_awvalid) |-> ##1 (!s_axi_awready until_with (int_wdone_wire && int_bdone_wire)));

  // WREADY behavior: drops after capture, stays low until AW and B are done
  assert property ((s_axi_wready && s_axi_wvalid) |-> ##1 (!s_axi_wready until_with (int_awdone_wire && int_bdone_wire)));

  // BVALID generation/hold/clear
  assert property ((int_awdone_wire && int_wdone_wire) |=> s_axi_bvalid);
  assert property (s_axi_bvalid && !s_axi_bready |=> s_axi_bvalid);
  assert property (s_axi_bvalid && s_axi_bready && !(int_awdone_wire && int_wdone_wire) |=> !s_axi_bvalid);

  // Coverage
  sequence aw_hs; s_axi_awvalid && s_axi_awready; endsequence
  sequence w_hs;  s_axi_wvalid  && s_axi_wready;  endsequence
  sequence b_hs;  s_axi_bvalid  && s_axi_bready;  endsequence

  // Reset then enable
  cover property (!aresetn ##1 aresetn);

  // AW then W then B
  cover property (aw_hs ##[1:10] w_hs ##[1:10] b_hs);

  // W then AW then B
  cover property (w_hs ##[1:10] aw_hs ##[1:10] b_hs);

  // Simultaneous AW & W then B
  cover property ((s_axi_awvalid && s_axi_wvalid && s_axi_awready && s_axi_wready) ##[0:5] b_hs);

  // B backpressure for 3 cycles
  cover property (s_axi_bvalid && !s_axi_bready [*3] ##1 s_axi_bvalid && s_axi_bready);

  // Observe TVALID pulse
  cover property ($rose(m_axis_tvalid));

endmodule