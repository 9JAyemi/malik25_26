// SVA checker for ao22: q = (i0 & i1) | (i2 & i3)
module ao22_sva;
  // Sample on any relevant change
  default clocking cb @(i0 or i1 or i2 or i3 or int_0n[0] or int_0n[1] or q); endclocking

  // Functional equivalence (4-state)
  a_top_equiv:  assert property (q === ((i0 & i1) | (i2 & i3)))
                 else $error("ao22: q != (i0&i1)|(i2&i3)");

  // Gate-by-gate equivalence (internal nets)
  a_and0_equiv: assert property (int_0n[0] === (i0 & i1))
                 else $error("ao22: int_0n[0] != i0&i1");
  a_and1_equiv: assert property (int_0n[1] === (i2 & i3))
                 else $error("ao22: int_0n[1] != i2&i3");
  a_or_equiv:   assert property (q === (int_0n[0] | int_0n[1]))
                 else $error("ao22: q != int_0n[0]|int_0n[1]");

  // Knownness: if inputs are 0/1, outputs are 0/1
  a_known:      assert property (!$isunknown({i0,i1,i2,i3}) |-> !$isunknown({int_0n,q}))
                 else $error("ao22: X/Z on outputs with known inputs");

  // Dominance and zero conditions
  a_term0_dom:  assert property ((i0 && i1) |-> q);
  a_term1_dom:  assert property ((i2 && i3) |-> q);
  a_zero_when0: assert property (((!i0 || !i1) && (!i2 || !i3)) |-> !q);

  // Functional coverage
  c_only_t0:    cover property ((i0 && i1) && !(i2 && i3) && q);
  c_only_t1:    cover property ((i2 && i3) && !(i0 && i1) && q);
  c_both:       cover property ((i0 && i1) &&  (i2 && i3) && q);
  c_neither:    cover property ((! (i0 && i1)) && (! (i2 && i3)) && !q);
  c_q_rise:     cover property (!q ##1 q);
  c_q_fall:     cover property ( q ##1 !q);
endmodule

// Bind into the DUT
bind ao22 ao22_sva ao22_sva_i();