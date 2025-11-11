// SVA for bw_r_irf_register and variants
// Concise, key checks and coverage. Bind this file in your sim.
// Focuses on write effects, save/restore semantics, gating, muxing, and basic coverage.

`ifndef SYNTHESIS

module bw_r_irf_register_sva (input logic clk);

  // Warmups to make $past safe
  logic pos_ok, neg_ok;
  initial begin pos_ok=0; neg_ok=0; end
  always @(posedge clk) pos_ok <= 1;
  always @(negedge clk) neg_ok <= 1;

`ifdef FPGA_SYN_1THREAD

  // Common single-thread checks
  // onereg write behavior
  assert property (@(posedge clk) disable iff(!pos_ok)
                   wr_en |=> onereg == $past(wrdata));
  assert property (@(posedge clk) disable iff(!pos_ok)
                   !wr_en |=> onereg == $past(onereg));

  // rd_data mirrors onereg
  assert property (@(posedge clk) rd_data == onereg);

  // Minimal coverage
  cover property (@(posedge clk) wr_en);
  cover property (@(posedge clk) restore);

`ifdef FPGA_SYN_SAVE_BRAM
  // BRAM-split window variant
  // Shorthand for current address selection (sampled on negedge)
  let addr_sel = (save ? save_addr : restore_addr);
  let addr1_now = {1'b1, addr_sel};
  let addr0_now = {1'b0, addr_sel};

  // Save: write window halves on negedge
  assert property (@(negedge clk) disable iff(!neg_ok)
                   save |=> window[$past(addr1_now)] == $past(wren ? wr_data[71:36] : rd_data[71:36]));
  assert property (@(negedge clk) disable iff(!neg_ok)
                   save |=> window[$past(addr0_now)] == $past(wren ? wr_data[35:0]  : rd_data[35:0]));

  // Restore-data load from window on negedge when not saving
  assert property (@(negedge clk) disable iff(!neg_ok)
                   !save |=> restore_data[71:36] == $past(window[$past(addr1_now)]));
  assert property (@(negedge clk) disable iff(!neg_ok)
                   !save |=> restore_data[35:0]  == $past(window[$past(addr0_now)]));

  // Coverage for both save/restore paths
  cover property (@(negedge clk) save);
  cover property (@(negedge clk) !save);
`else
  // 1-thread, full-width window variant
  // Gating on restore vs same address
  assert property (@(posedge clk) (restore && (wr_addr == rd_addr)) |-> !wr_en);
  assert property (@(posedge clk) (restore && (wr_addr != rd_addr)) |->  wr_en);

  // Save: write window on negedge
  assert property (@(negedge clk) disable iff(!neg_ok)
                   save_d |=> window[$past(wr_addr)] == $past(rd_data));

  // Restore-data equals selected window entry at all times
  assert property (@(posedge clk) restore_data == window[rd_addr]);

  // Coverage: direct write, restore write, same-address block
  cover property (@(posedge clk) wren);
  cover property (@(posedge clk) restore && (wr_addr != rd_addr));
  cover property (@(posedge clk) restore && (wr_addr == rd_addr));
  cover property (@(negedge clk) save_d);
`endif

`else  // Multi-thread variant

  // rd_data muxing correctness
  assert property (@(posedge clk) (rd_thread==2'b00) |-> (rd_data==reg_th0));
  assert property (@(posedge clk) (rd_thread==2'b01) |-> (rd_data==reg_th1));
  assert property (@(posedge clk) (rd_thread==2'b10) |-> (rd_data==reg_th2));
  assert property (@(posedge clk) (rd_thread==2'b11) |-> (rd_data==reg_th3));

  // Save: window write on negedge
  assert property (@(negedge clk) disable iff(!neg_ok)
                   save_d |=> window[$past(wr_addr)] == $past(save_data));

  // Per-thread write behavior and gating
  // th0
  assert property (@(posedge clk) disable iff(!pos_ok)
                   wr_en[0] |=> reg_th0 == $past(wrdata0));
  assert property (@(posedge clk) disable iff(!pos_ok)
                   !wr_en[0] |=> reg_th0 == $past(reg_th0));
  assert property (@(posedge clk)
                   restore && (rd_addr[4:3]==2'b00) && (wr_addr==rd_addr) |-> !wr_en[0]);
  assert property (@(posedge clk)
                   restore && (rd_addr[4:3]==2'b00) && (wr_addr!=rd_addr) |->  wr_en[0]);
  assert property (@(posedge clk) disable iff(!pos_ok)
                   wr_en[0] && restores[0] |=> reg_th0 == $past(restore_data));

  // th1
  assert property (@(posedge clk) disable iff(!pos_ok)
                   wr_en[1] |=> reg_th1 == $past(wrdata1));
  assert property (@(posedge clk) disable iff(!pos_ok)
                   !wr_en[1] |=> reg_th1 == $past(reg_th1));
  assert property (@(posedge clk)
                   restore && (rd_addr[4:3]==2'b01) && (wr_addr==rd_addr) |-> !wr_en[1]);
  assert property (@(posedge clk)
                   restore && (rd_addr[4:3]==2'b01) && (wr_addr!=rd_addr) |->  wr_en[1]);
  assert property (@(posedge clk) disable iff(!pos_ok)
                   wr_en[1] && restores[1] |=> reg_th1 == $past(restore_data));

  // th2
  assert property (@(posedge clk) disable iff(!pos_ok)
                   wr_en[2] |=> reg_th2 == $past(wrdata2));
  assert property (@(posedge clk) disable iff(!pos_ok)
                   !wr_en[2] |=> reg_th2 == $past(reg_th2));
  assert property (@(posedge clk)
                   restore && (rd_addr[4:3]==2'b10) && (wr_addr==rd_addr) |-> !wr_en[2]);
  assert property (@(posedge clk)
                   restore && (rd_addr[4:3]==2'b10) && (wr_addr!=rd_addr) |->  wr_en[2]);
  assert property (@(posedge clk) disable iff(!pos_ok)
                   wr_en[2] && restores[2] |=> reg_th2 == $past(restore_data));

  // th3
  assert property (@(posedge clk) disable iff(!pos_ok)
                   wr_en[3] |=> reg_th3 == $past(wrdata3));
  assert property (@(posedge clk) disable iff(!pos_ok)
                   !wr_en[3] |=> reg_th3 == $past(reg_th3));
  assert property (@(posedge clk)
                   restore && (rd_addr[4:3]==2'b11) && (wr_addr==rd_addr) |-> !wr_en[3]);
  assert property (@(posedge clk)
                   restore && (rd_addr[4:3]==2'b11) && (wr_addr!=rd_addr) |->  wr_en[3]);
  assert property (@(posedge clk) disable iff(!pos_ok)
                   wr_en[3] && restores[3] |=> reg_th3 == $past(restore_data));

  // save_data must reflect selected thread register
  assert property (@(posedge clk)
                   (wr_addr[4:3]==2'b00) |-> (save_data==reg_th0));
  assert property (@(posedge clk)
                   (wr_addr[4:3]==2'b01) |-> (save_data==reg_th1));
  assert property (@(posedge clk)
                   (wr_addr[4:3]==2'b10) |-> (save_data==reg_th2));
  assert property (@(posedge clk)
                   (wr_addr[4:3]==2'b11) |-> (save_data==reg_th3));

  // Coverage: direct writes, restore writes, same-addr hazard, save event
  cover property (@(posedge clk) (wrens!=4'b0));
  cover property (@(posedge clk) restore && (wr_addr!=rd_addr));
  cover property (@(posedge clk) restore && (wr_addr==rd_addr));
  cover property (@(negedge clk) save_d);

`endif // !FPGA_SYN_1THREAD

endmodule

// Bind to DUT
bind bw_r_irf_register bw_r_irf_register_sva i_bw_r_irf_register_sva(.clk(clk));

`endif // SYNTHESIS