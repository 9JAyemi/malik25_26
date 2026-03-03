// SVA for bitwise_or. Bind this to the DUT.
module bitwise_or_sva (bitwise_or dut);
  // Combinational sampling event (avoids races with ##0)
  event comb_ev;
  always @* -> comb_ev;

  // Core functional check (4-state accurate)
  ap_or_eq: assert property (@(comb_ev) 1'b1 |-> ##0 (dut.c === (dut.a | dut.b)));

  // If inputs are all known, output must be fully known
  ap_known_out: assert property (@(comb_ev) ##0 (!$isunknown({dut.a,dut.b})) |-> !$isunknown(dut.c));

  // Truth-table coverage (any bit position)
  cover_00: cover property (@(comb_ev) ##0 ((~dut.a & ~dut.b & ~dut.c) != 8'h00));
  cover_01: cover property (@(comb_ev) ##0 ((~dut.a &  dut.b &  dut.c) != 8'h00));
  cover_10: cover property (@(comb_ev) ##0 (( dut.a & ~dut.b &  dut.c) != 8'h00));
  cover_11: cover property (@(comb_ev) ##0 (( dut.a &  dut.b &  dut.c) != 8'h00));

  // Useful vector corner cases
  cover_zero:   cover property (@(comb_ev) ##0 (dut.a==8'h00 && dut.b==8'h00 && dut.c==8'h00));
  cover_pass_a: cover property (@(comb_ev) ##0 (dut.a==8'hFF && dut.b==8'h00 && dut.c==8'hFF));
  cover_pass_b: cover property (@(comb_ev) ##0 (dut.a==8'h00 && dut.b==8'hFF && dut.c==8'hFF));
  cover_mix:    cover property (@(comb_ev) ##0 (dut.a==8'hAA && dut.b==8'h55 && dut.c==8'hFF));

  // X/Z propagation/override coverage
  cover_ax_b0: cover property (@(comb_ev) ##0 ($isunknown(dut.a) && dut.b==8'h00 && $isunknown(dut.c)));
  cover_bx_a0: cover property (@(comb_ev) ##0 ($isunknown(dut.b) && dut.a==8'h00 && $isunknown(dut.c)));
  cover_ax_bf: cover property (@(comb_ev) ##0 ($isunknown(dut.a) && dut.b==8'hFF && dut.c==8'hFF));
  cover_bx_af: cover property (@(comb_ev) ##0 ($isunknown(dut.b) && dut.a==8'hFF && dut.c==8'hFF));
endmodule

bind bitwise_or bitwise_or_sva sva_bitwise_or();