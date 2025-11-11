// SystemVerilog Assertions for dpth_addr
// Bind into the DUT scope: bind dpth_addr dpth_addr_sva sva();

module dpth_addr_sva;

  // Use DUT signals directly (bound into dpth_addr scope)
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Asynchronous reset behavior checked at clock edge (no disable)
  a_async_reset_zero: assert property (@(posedge clk) !rst_n |-> (rat==8'h00 && pc==8'h00));

  // Combinational definitions (checked when out of reset)
  a_comb_m_at:         assert property (m_at == (pc_at ? rat : pc));
  a_comb_low_sum:      assert property (low_sum == ir_low + rx_low);
  a_comb_pc_plus_one:  assert property (pc_plus_one == m_at + 8'd1);

  // No X/Z on key state/outputs after reset is high
  a_no_unknowns: assert property (!$isunknown({rat, pc, m_at, low_sum, pc_plus_one}));

  // State holds when not loading
  a_hold_when_idle: assert property (!ld_rat |=> (rat == $past(rat) && pc == $past(pc)));

  // Updates on ld_rat
  a_rat_updates: assert property (ld_rat |=> rat == $past(low_sum));
  a_pc_updates:  assert property (ld_rat |=> pc  == $past(pc_plus_one));

  // Writes are gated only by ld_rat (ld_pc must have no effect)
  a_rat_change_gated: assert property ((rat != $past(rat)) |-> $past(ld_rat));
  a_pc_change_gated:  assert property ((pc  != $past(pc))  |-> $past(ld_rat));

  // Path-specific pc update (mod-256)
  a_pc_from_pc_path:  assert property (ld_rat && !pc_at |=> pc == ($past(pc)  + 8'd1)[7:0]);
  a_pc_from_rat_path: assert property (ld_rat &&  pc_at |=> pc == ($past(rat) + 8'd1)[7:0]);

  // ----------------
  // Coverage
  // ----------------

  // See both MUX paths used
  c_m_at_pc:  cover property (pc_at==1'b0 && m_at==pc);
  c_m_at_rat: cover property (pc_at==1'b1 && m_at==rat);

  // Exercise both update paths for pc
  c_pc_from_pc:  cover property (ld_rat && !pc_at);
  c_pc_from_rat: cover property (ld_rat &&  pc_at);

  // rat load with addition (including carry)
  c_rat_load:        cover property (ld_rat);
  c_low_sum_carry:   cover property (ld_rat && (low_sum < ir_low)); // overflow on 8-bit add

  // pc increment wrap-around on pc path
  c_pc_wrap: cover property (ld_rat && !pc_at && ($past(pc)==8'hFF) |=> pc==8'h00);

  // Idle hold coverage (ld_pc may toggle but state holds when ld_rat==0)
  c_idle_hold: cover property (!ld_rat ##1 (rat==$past(rat) && pc==$past(pc)));
  c_ld_pc_tog: cover property ($changed(ld_pc));

endmodule

// Suggested bind (place in a separate file or your TB):
// bind dpth_addr dpth_addr_sva sva();