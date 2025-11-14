// Bindable SVA for sky130_fd_sc_hdll__and4
module and4_sva (
  input logic A, B, C, D,
  input logic X,
  input logic and0_out_X,
  input logic and1_out_X
);
  default clocking cb @(*); endclocking

  // Functional equivalence and structure
  assert property (X === (A & B & C & D));
  assert property (and0_out_X === (A & B & C));
  assert property (and1_out_X === (D & and0_out_X));
  assert property (X === and1_out_X);

  // 4-state semantics (dominance and known cases)
  assert property ((A===0 || B===0 || C===0 || D===0) |-> (X===0));
  assert property ((A===1 && B===1 && C===1 && D===1) |-> (X===1));
  assert property ((!(A===0 || B===0 || C===0 || D===0) && $isunknown({A,B,C,D})) |-> $isunknown(X));

  // No Z on nets (AND/BUF should never drive Z)
  assert property (X !== 1'bz && and0_out_X !== 1'bz && and1_out_X !== 1'bz);

  // Minimal, meaningful coverage
  cover property (X===0);
  cover property (X===1);
  cover property ((A===0 || B===0 || C===0 || D===0) && X===0); // zero-dominance observed
  cover property ((A===1 && B===1 && C===1 && D===1) && X===1); // all-ones observed
  cover property ($isunknown({A,B,C,D}) && !(A===0||B===0||C===0||D===0) && $isunknown(X)); // X-propagation
endmodule

// Bind into the DUT scope to access internal nets
bind sky130_fd_sc_hdll__and4 and4_sva and4_sva_i (.*);