// SVA for doublencomparator
// Bind this with a clock/reset in your environment.

module doublencomparator_sva (
  input logic clk, rst_n,
  input logic x0, x1, y0, y1,
  input logic eqin, gtin, ltin,
  input logic eqout, gtout, ltout
);
  default clocking cb @ (posedge clk); endclocking
  default disable iff (!rst_n)

  // Canonical spec (x0 is MSB, x1 is LSB)
  logic eq_spec, gt_spec, lt_spec;
  always_comb begin
    eq_spec = eqin & (x0 ~^ y0) & (x1 ~^ y1);
    gt_spec = (gtin | ({x0,x1} > {y0,y1})) & ~ltin;
    lt_spec = ltin | ~(eq_spec | gt_spec);
  end

  // Functional equivalence
  assert property (eqout == eq_spec);
  assert property (gtout == gt_spec);
  assert property (ltout == lt_spec);

  // Key invariants
  assert property (gtout |-> !ltout);
  assert property ((!eqout && !gtout) |-> ltout);

  // Combinational purity and no-X propagation
  assert property ($stable({x0,x1,y0,y1,eqin,gtin,ltin}) |=> $stable({eqout,gtout,ltout}));
  assert property (!$isunknown({x0,x1,y0,y1,eqin,gtin,ltin}) |-> !$isunknown({eqout,gtout,ltout}));

  // Coverage: equality, each GT subcase, LT propagation/defaults
  cover property (eqin && ({x0,x1} == {y0,y1}) && eqout);
  cover property (!ltin && !gtin && (x0 && !y0) && gtout);                               // MSB greater
  cover property (!ltin && !gtin && (!x0 && !y0 && x1 && !y1) && gtout);                // MSB=0, LSB greater
  cover property (!ltin && !gtin && (x0 && y0 && x1 && !y1) && gtout);                  // MSB=1, LSB greater
  cover property (ltin && !gtout && ltout);                                             // ltin blocks gt
  cover property (!gtin && !ltin && ({x0,x1} < {y0,y1}) && ltout);                      // default to lt
endmodule

bind doublencomparator doublencomparator_sva sva_i (
  .clk(clk), .rst_n(rst_n),
  .x0(x0), .x1(x1), .y0(y0), .y1(y1),
  .eqin(eqin), .gtin(gtin), .ltin(ltin),
  .eqout(eqout), .gtout(gtout), .ltout(ltout)
);