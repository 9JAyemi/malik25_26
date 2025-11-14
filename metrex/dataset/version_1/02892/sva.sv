// SVA for my_module
module my_module_sva (
  input logic clk,
  input logic in,
  input logic fr_a,
  input logic fr_b,
  input logic fr_chk
);
  default clocking cb @(posedge clk); endclocking

  // Functional correctness (safe from first edge using 1 |=>)
  a_fr_a:   assert property (1 |=> fr_a   == $past(in));
  a_fr_b:   assert property (1 |=> fr_b   == $past(in));
  a_fr_chk: assert property (1 |=> fr_chk == ~ $past(in)); // since fr_chk <= in + 1 (1-bit)

  // Internal consistency
  a_ab_eq:  assert property (1 |=> fr_a == fr_b);
  a_chk_rel:assert property (1 |=> (fr_chk == ~fr_a) && (fr_chk == ~fr_b));

  // No X/Z on outputs when sampled input was known
  a_no_x:   assert property (!$isunknown($past(in)) |-> (!$isunknown(fr_a) && !$isunknown(fr_b) && !$isunknown(fr_chk)));

  // Coverage
  c_in0:    cover  property (1 |=> ($past(in)==0 && fr_a==0 && fr_b==0 && fr_chk==1));
  c_in1:    cover  property (1 |=> ($past(in)==1 && fr_a==1 && fr_b==1 && fr_chk==0));
  c_toggle: cover  property ($changed(in) |=> (fr_a==$past(in) && fr_b==$past(in) && fr_chk==~$past(in)));
endmodule

// Bind into DUT
bind my_module my_module_sva sva_i (.clk(clk), .in(in), .fr_a(fr_a), .fr_b(fr_b), .fr_chk(fr_chk));