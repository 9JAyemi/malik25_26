// SVA for module stack
// Bind into the DUT; accesses internal regs/mem
module stack_sva;
  // use DUT scope via bind
  default clocking cb @(posedge clock); endclocking
  default disable iff (reset);

  // Sanity
  initial assert (PTR == $clog2(DEPTH)) else $error("PTR != $clog2(DEPTH)");

  // Invariants
  a_nsp_rel:         assert property (nsp == sp - 1);
  a_tos_out_map:     assert property (tos_out == cells[sp]);
  a_nos_out_map:     assert property (nos_out == cells[nsp]);

  // Pointer next-state rules
  a_sp_dec:          assert property ((nip && !dup) |=> sp == $past(sp) - 1);
  a_sp_inc:          assert property ((dup && !nip) |=> sp == $past(sp) + 1);
  a_sp_hold_both:    assert property ((dup &&  nip) |=> sp == $past(sp));
  a_sp_hold_idle:    assert property ((!dup && !nip) |=> sp == $past(sp));

  // Prevent underflow/overflow
  a_no_underflow:    assert property ((sp == '0)              |-> !(nip && !dup));
  a_no_overflow:     assert property ((sp == DEPTH-1)         |-> !(dup && !nip));

  // Registered views
  a_nos_next:        assert property (1 |=> nos == $past(nos_out));
  a_tos_we:          assert property (we |=> tos == $past(data_in));
  a_tos_both:        assert property ((dup && nip && !we) |=> tos == $past(nos));
  a_tos_default:     assert property ((!we && !(dup && nip)) |=> tos == $past(tos_out));

  // Memory write effects
  a_mem_write_sp:    assert property (1 |=> cells[$past(sp)]  == $past(tos));
  a_mem_write_nsp:   assert property ((dup && nip) |=> cells[$past(nsp)] == $past(tos));

  // Output transitions per op
  a_nip_moves_down:  assert property ((nip && !dup) |=> tos_out == $past(nos_out));
  a_dup_sets_nos:    assert property ((dup && !nip) |=> nos_out == $past(tos_out));
  a_both_dup_top2:   assert property ((dup &&  nip) |=> (tos_out == $past(tos) && nos_out == $past(tos)));
  a_idle_stable:     assert property ((!dup && !nip) |=> (tos_out == $past(tos_out) && nos_out == $past(nos_out)));

  // Wrap behavior
  a_nsp_wrap:        assert property ((sp == '0) |-> nsp == DEPTH-1);

  // Coverage
  c_nip:             cover property (!reset ##1 (nip && !dup));
  c_dup:             cover property (!reset ##1 (dup && !nip));
  c_both:            cover property (!reset ##1 (dup &&  nip));
  c_we:              cover property (!reset ##1 we);
  c_sp_lo:           cover property (sp == '0);
  c_sp_hi:           cover property (sp == DEPTH-1);
endmodule

bind stack stack_sva;