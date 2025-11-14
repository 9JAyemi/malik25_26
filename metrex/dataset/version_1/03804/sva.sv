// SVA checker for mux_2to1
module mux_2to1_sva (
  input logic a, b, c, d,
  input logic x, y, z
);

  // Fire checks on any input change
  event comb_ev;
  always @(a or b or c or d) -> comb_ev;

  // Functional correctness (4-state accurate)
  assert property (@(comb_ev) x === (c ? a : b));
  assert property (@(comb_ev) y === (c ? b : a));
  assert property (@(comb_ev) z === (c ? d : b));

  // No spurious output toggles without dependent input change
  assert property (@(posedge x or negedge x) $changed({a,b,c}));
  assert property (@(posedge y or negedge y) $changed({a,b,c}));
  assert property (@(posedge z or negedge z) $changed({b,c,d}));

  // Determinism when select and selected data are known
  assert property (@(comb_ev) (c===1 && !$isunknown(a)) |-> (x==a && !$isunknown(x)));
  assert property (@(comb_ev) (c===0 && !$isunknown(b)) |-> (x==b && !$isunknown(x)));
  assert property (@(comb_ev) (c===1 && !$isunknown(b)) |-> (y==b && !$isunknown(y)));
  assert property (@(comb_ev) (c===0 && !$isunknown(a)) |-> (y==a && !$isunknown(y)));
  assert property (@(comb_ev) (c===1 && !$isunknown(d)) |-> (z==d && !$isunknown(z)));
  assert property (@(comb_ev) (c===0 && !$isunknown(b)) |-> (z==b && !$isunknown(z)));

  // X-robustness when c is unknown but data resolve the choice
  assert property (@(comb_ev) ($isunknown(c) && (a===b)) |-> (x==a && y==a));
  assert property (@(comb_ev) ($isunknown(c) && (d===b)) |-> (z==b));

  // Outputs never unknown when all inputs are known
  assert property (@(comb_ev) !$isunknown({a,b,c,d}) |-> !$isunknown({x,y,z}));

  // Simple relational sanity
  assert property (@(comb_ev) (a===b) |-> (x===y));

  // Coverage: both select paths exercised and c toggles
  cover property (@(comb_ev) (c==0) ##0 (x==b && y==a && z==b));
  cover property (@(comb_ev) (c==1) ##0 (x==a && y==b && z==d));
  cover property (@(comb_ev) $changed(c));

endmodule

// Bind into the DUT
bind mux_2to1 mux_2to1_sva i_mux_2to1_sva (.a(a),.b(b),.c(c),.d(d),.x(x),.y(y),.z(z));