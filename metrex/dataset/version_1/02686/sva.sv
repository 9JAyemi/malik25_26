// SVA for wb_adapter: concise, thorough pass-through and reset checks
module wb_adapter_sva (
  input clk, input rst,
  input [31:0] wbm_adr_i, wbm_dat_i,
  input        wbm_we_i, wbm_stb_i,
  input [3:0]  wbm_sel_i,
  input [31:0] wbs_dat_i,
  input        wbs_ack_i, wbs_err_i, wbs_rty_i,
  input [31:0] wbm_dat_o,
  input        wbm_ack_o, wbm_err_o, wbm_rty_o,
  input [31:0] wbs_adr_o, wbs_dat_o,
  input        wbs_we_o, wbs_stb_o, wbs_cyc_o,
  input [3:0]  wbs_sel_o
);

  // Reset: next-cycle zeroing and hold-zero while asserted
  assert property (@(posedge clk) rst |=> (wbm_dat_o==32'b0 && !wbm_ack_o && !wbm_err_o && !wbm_rty_o &&
                                           wbs_adr_o==32'b0 && wbs_dat_o==32'b0 && !wbs_we_o &&
                                           wbs_sel_o==4'b0 && !wbs_stb_o && !wbs_cyc_o));
  assert property (@(posedge clk) (rst && $past(rst)) |-> (wbm_dat_o==32'b0 && !wbm_ack_o && !wbm_err_o && !wbm_rty_o &&
                                                          wbs_adr_o==32'b0 && wbs_dat_o==32'b0 && !wbs_we_o &&
                                                          wbs_sel_o==4'b0 && !wbs_stb_o && !wbs_cyc_o));

  // Structural invariant: cyc mirrors stb in this adapter
  assert property (@(posedge clk) (wbs_cyc_o == wbs_stb_o));

  // One-cycle registered pass-through (start checking only after a clean cycle post-reset)
  // Master->Slave path
  assert property (@(posedge clk) disable iff (rst) $past(!rst) |-> (wbs_adr_o == $past(wbm_adr_i)));
  assert property (@(posedge clk) disable iff (rst) $past(!rst) |-> (wbs_dat_o == $past(wbm_dat_i)));
  assert property (@(posedge clk) disable iff (rst) $past(!rst) |-> (wbs_we_o  == $past(wbm_we_i)));
  assert property (@(posedge clk) disable iff (rst) $past(!rst) |-> (wbs_sel_o == $past(wbm_sel_i)));
  assert property (@(posedge clk) disable iff (rst) $past(!rst) |-> (wbs_stb_o == $past(wbm_stb_i)));
  assert property (@(posedge clk) disable iff (rst) $past(!rst) |-> (wbs_cyc_o == $past(wbm_stb_i)));

  // Slave->Master path
  assert property (@(posedge clk) disable iff (rst) $past(!rst) |-> (wbm_dat_o == $past(wbs_dat_i)));
  assert property (@(posedge clk) disable iff (rst) $past(!rst) |-> (wbm_ack_o == $past(wbs_ack_i)));
  assert property (@(posedge clk) disable iff (rst) $past(!rst) |-> (wbm_err_o == $past(wbs_err_i)));
  assert property (@(posedge clk) disable iff (rst) $past(!rst) |-> (wbm_rty_o == $past(wbs_rty_i)));

  // Sanity: outputs not X/Z after reset released
  assert property (@(posedge clk) disable iff (rst)
                   !$isunknown({wbm_dat_o, wbm_ack_o, wbm_err_o, wbm_rty_o,
                                wbs_adr_o, wbs_dat_o, wbs_we_o, wbs_sel_o, wbs_stb_o, wbs_cyc_o}));

  // Coverage: demonstrate typical activity and pass-through behavior
  cover property (@(posedge clk) disable iff (rst) $rose(wbm_stb_i) ##1 (wbs_stb_o && wbs_cyc_o));
  cover property (@(posedge clk) disable iff (rst) $changed(wbm_dat_i) ##1 (wbs_dat_o == $past(wbm_dat_i)));
  cover property (@(posedge clk) disable iff (rst) $changed(wbs_dat_i) ##1 (wbm_dat_o == $past(wbs_dat_i)));
  cover property (@(posedge clk) disable iff (rst) $rose(wbs_ack_i) ##1 $rose(wbm_ack_o));
  cover property (@(posedge clk) disable iff (rst) $rose(wbs_err_i) ##1 $rose(wbm_err_o));
  cover property (@(posedge clk) disable iff (rst) $rose(wbs_rty_i) ##1 $rose(wbm_rty_o));

endmodule

// Bind into the DUT
bind wb_adapter wb_adapter_sva sva (
  .clk(clk), .rst(rst),
  .wbm_adr_i(wbm_adr_i), .wbm_dat_i(wbm_dat_i),
  .wbm_we_i(wbm_we_i), .wbm_stb_i(wbm_stb_i), .wbm_sel_i(wbm_sel_i),
  .wbs_dat_i(wbs_dat_i), .wbs_ack_i(wbs_ack_i), .wbs_err_i(wbs_err_i), .wbs_rty_i(wbs_rty_i),
  .wbm_dat_o(wbm_dat_o), .wbm_ack_o(wbm_ack_o), .wbm_err_o(wbm_err_o), .wbm_rty_o(wbm_rty_o),
  .wbs_adr_o(wbs_adr_o), .wbs_dat_o(wbs_dat_o), .wbs_we_o(wbs_we_o),
  .wbs_sel_o(wbs_sel_o), .wbs_stb_o(wbs_stb_o), .wbs_cyc_o(wbs_cyc_o)
);