// SVA for d_ff_jk_with_async_set_reset
module d_ff_jk_with_async_set_reset_sva (
  input logic clk,
  input logic d,
  input logic aset,
  input logic areset,
  input logic q,
  input logic j,
  input logic k
);
  default clocking cb @(posedge clk); endclocking

  // Control priority/effects (synchronous)
  assert property (aset |-> q == 1'b1);
  assert property (!aset && areset |-> q == 1'b0);
  assert property (aset && areset |-> q == 1'b1); // set dominates reset

  // j,k update/hold behavior
  assert property ($past(1'b1) && !aset && !areset |-> j == $past(d) && k == ~$past(d) && j == ~k);
  assert property ($past(1'b1) && (aset || areset) |-> j == $past(j) && k == $past(k));

  // q next-state function in normal mode: q == $past(j ^ (q & ~k))
  assert property ($past(1'b1) && !aset && !areset |-> q == $past(j ^ (q & ~k)));

  // Sanity: no X on controls and data at clock edge
  assert property (!$isunknown({aset, areset, d}));

  // Coverage
  cover property (aset && !areset);
  cover property (areset && !aset);
  cover property (aset && areset);
  cover property ($past(1'b1) && !aset && !areset && $past(!aset && !areset) && $past(q)==1'b0 && $past(d)==1'b1 && q==1'b1); // 0->1
  cover property ($past(1'b1) && !aset && !areset && $past(!aset && !areset) && $past(q)==1'b1 && q==1'b0); // 1->0
  cover property ($past(1'b1) && !aset && !areset && $past(!aset && !areset) && $past(q)==1'b0 && $past(d)==1'b0 && q==1'b0); // 0->0
endmodule

bind d_ff_jk_with_async_set_reset d_ff_jk_with_async_set_reset_sva sva_i (
  .clk(clk),
  .d(d),
  .aset(aset),
  .areset(areset),
  .q(q),
  .j(j),
  .k(k)
);