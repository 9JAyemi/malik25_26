// SVA for ripple_carry_adder
// Bind into DUT scope; uses an event to sample after comb settle (##0)

module rca_sva;
  event comb_ev;
  always @(a or b or cin) -> comb_ev;

  // Known-in -> known-out
  assert property (@(comb_ev) (!$isunknown({a,b,cin})) |-> ##0 (!$isunknown({sum,cout,c})));

  // Full arithmetic correctness (will catch missing MSB carry in DUT)
  assert property (@(comb_ev) disable iff ($isunknown({a,b,cin}))
                   ##0 {cout,sum} == ({1'b0,a} + {1'b0,b} + cin));

  // Ripple-carry chain correctness
  assert property (@(comb_ev) disable iff ($isunknown({a,b,cin})) ##0 c[0] == cin);
  assert property (@(comb_ev) disable iff ($isunknown({a,b,cin})) ##0
                   c[1] == ((a[0] & b[0]) | (cin & (a[0]^b[0]))));
  assert property (@(comb_ev) disable iff ($isunknown({a,b,cin})) ##0
                   c[2] == ((a[1] & b[1]) | (c[1] & (a[1]^b[1]))));
  assert property (@(comb_ev) disable iff ($isunknown({a,b,cin})) ##0
                   c[3] == ((a[2] & b[2]) | (c[2] & (a[2]^b[2]))));

  // Sum-bit correctness against ripple carries
  assert property (@(comb_ev) disable iff ($isunknown({a,b,cin})) ##0
                   sum[0] == (a[0]^b[0]^cin));
  assert property (@(comb_ev) disable iff ($isunknown({a,b,cin})) ##0
                   sum[1] == (a[1]^b[1]^c[1]));
  assert property (@(comb_ev) disable iff ($isunknown({a,b,cin})) ##0
                   sum[2] == (a[2]^b[2]^c[2]));
  assert property (@(comb_ev) disable iff ($isunknown({a,b,cin})) ##0
                   sum[3] == (a[3]^b[3]^c[3]));

  // Wiring check
  assert property (@(comb_ev) ##0 cout == c[3]);

  // Functional coverage
  cover property (@(comb_ev) disable iff ($isunknown({a,b,cin}))
                  ##0 (({1'b0,a}+{1'b0,b}+cin)[4] == 0 && cout==0));
  cover property (@(comb_ev) disable iff ($isunknown({a,b,cin}))
                  ##0 (({1'b0,a}+{1'b0,b}+cin)[4] == 1));
  cover property (@(comb_ev) disable iff ($isunknown({a,b,cin}))
                  (a==4'h0 && b==4'h0 && !cin) ##0 (sum==4'h0 && !cout));
  // Full-chain propagate (all P=1) with cin=1
  cover property (@(comb_ev) disable iff ($isunknown({a,b,cin}))
                  (cin && ((a^b)==4'hF) && ((a & b)==4'h0)) ##0 cout);
  // MSB generate (exposes DUT's missing final carry if present)
  cover property (@(comb_ev) disable iff ($isunknown({a,b,cin}))
                  (!cin && a==4'h8 && b==4'h8) ##0 1'b1);
endmodule

bind ripple_carry_adder rca_sva rca_sva_i();