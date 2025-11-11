// SVA for tg68_ram: concise, high-signal-quality checks and coverage.
// Bind into DUT; uses internal regs/arrays directly.
module tg68_ram_sva #(parameter MS=512) ();

  default clocking cb @(posedge clk); endclocking

  // Control integrity and alignment
  a_no_x_ctrl:   assert property (disable iff ($initstate) !tg68_as |-> !$isunknown({tg68_rw,tg68_uds,tg68_lds,tg68_adr}));
  a_align:       assert property (disable iff ($initstate) !tg68_as |-> tg68_adr[0]==1'b0);
  a_stable_addr: assert property (disable iff ($initstate) $rose(!tg68_as) |-> $stable(tg68_adr) throughout (!tg68_as));
  a_stable_rw:   assert property (disable iff ($initstate) $rose(!tg68_as) |-> $stable(tg68_rw) throughout (!tg68_as));
  a_stable_be:   assert property (disable iff ($initstate) $rose(!tg68_as) |-> $stable({tg68_uds,tg68_lds}) throughout (!tg68_as));

  // Handshake pipeline and definition
  a_trn_dly:     assert property (disable iff ($initstate) trn == $past(tg68_as));
  a_ack_dly:     assert property (disable iff ($initstate) ack == $past(trn));
  a_dtack_def:   assert property (disable iff ($initstate) tg68_dtack == (ack || tg68_as));
  a_dtack_as_hi: assert property (disable iff ($initstate) tg68_as |-> tg68_dtack);
  a_dtack_low2:  assert property (disable iff ($initstate) (!tg68_as && $past(!tg68_as)) |-> !tg68_dtack);

  // Read datapath
  a_read_data:   assert property (disable iff ($initstate) (!tg68_as && tg68_rw) |=> mem_do == {mem1[$past(tg68_adr[31:1])], mem0[$past(tg68_adr[31:1])]});
  a_din_eq_do:   assert property (disable iff ($initstate) tg68_dat_in == mem_do);
  a_do_only_on_rd: assert property (disable iff ($initstate) $changed(mem_do) |-> $past(!tg68_as && tg68_rw));

  // Write effects per byte lane
  a_wr_hi:       assert property (disable iff ($initstate) (!tg68_as && !tg68_rw && !tg68_uds) |=> mem1[$past(tg68_adr[31:1])] == $past(tg68_dat_out[15:8]));
  a_wr_lo:       assert property (disable iff ($initstate) (!tg68_as && !tg68_rw && !tg68_lds) |=> mem0[$past(tg68_adr[31:1])] == $past(tg68_dat_out[7:0]));
  a_no_wr_hi:    assert property (disable iff ($initstate) (!tg68_as && !tg68_rw && tg68_uds)  |=> mem1[$past(tg68_adr[31:1])] == $past(mem1[$past(tg68_adr[31:1])]));
  a_no_wr_lo:    assert property (disable iff ($initstate) (!tg68_as && !tg68_rw && tg68_lds)  |=> mem0[$past(tg68_adr[31:1])] == $past(mem0[$past(tg68_adr[31:1])]));

  // Functional coverage
  c_read:     cover property (!tg68_as && tg68_rw);
  c_wr_word:  cover property (!tg68_as && !tg68_rw && !tg68_uds && !tg68_lds);
  c_wr_hi:    cover property (!tg68_as && !tg68_rw && !tg68_uds &&  tg68_lds);
  c_wr_lo:    cover property (!tg68_as && !tg68_rw &&  tg68_uds && !tg68_lds);
  c_len3_acc: cover property ($rose(!tg68_as) ##1 (!tg68_as)[*2] ##1 tg68_as);

endmodule

bind tg68_ram tg68_ram_sva #(.MS(MS)) tg68_ram_sva_i();