// SVA for MUX4/MUX2x1. Bind into DUT; no DUT changes needed.

// Assertions for 2:1 MUX primitive (binds to all MUX2x1 instances)
module MUX2x1_sva;

  function automatic logic x_mux2(input logic a, b, s);
    if (s === 1'b0) x_mux2 = a;
    else if (s === 1'b1) x_mux2 = b;
    else x_mux2 = (a === b) ? a : 1'bx;
  endfunction

  default clocking cb @(A or B or S or Q); endclocking

  // Functional equivalence and X-merge semantics
  a_func:    assert property (Q === x_mux2(A, B, S));

  // No-X on known select path
  a_kn0:     assert property ((S === 1'b0 && !$isunknown(A)) |-> !$isunknown(Q));
  a_kn1:     assert property ((S === 1'b1 && !$isunknown(B)) |-> !$isunknown(Q));

  // Coverage
  c_sel0:    cover property (S === 1'b0 && Q === A);
  c_sel1:    cover property (S === 1'b1 && Q === B);
  c_selx:    cover property ((S !== 1'b0 && S !== 1'b1) && (A !== B) && $isunknown(Q));

endmodule

bind MUX2x1 MUX2x1_sva mux2x1_sva_i();

// Assertions for 4:1 MUX wrapper (binds to MUX4)
module MUX4_sva;

  function automatic logic x_mux2(input logic a, b, s);
    if (s === 1'b0) x_mux2 = a;
    else if (s === 1'b1) x_mux2 = b;
    else x_mux2 = (a === b) ? a : 1'bx;
  endfunction

  function automatic logic x_mux4(input logic A, B, C, D, S0, S1);
    logic m0, m1;
    m0 = x_mux2(A, B, S0);
    m1 = x_mux2(C, D, S0);
    x_mux4 = x_mux2(m0, m1, S1);
  endfunction

  default clocking cb @(A or B or C or D or S0 or S1 or Y or MUX0_out or MUX1_out); endclocking

  // Full functional equivalence to X-aware 4:1 spec
  a_y_func:  assert property (Y === x_mux4(A, B, C, D, S0, S1));

  // Stage outputs match expected X-aware behavior
  a_m0:      assert property (MUX0_out === x_mux2(A, B, S0));
  a_m1:      assert property (MUX1_out === x_mux2(C, D, S0));

  // If mids equal, S1 doesn't matter; if S1 is X and mids differ, Y must be X
  a_same:    assert property ((MUX0_out === MUX1_out) |-> (Y === MUX0_out));
  a_s1x:     assert property ((S1 !== 1'b0 && S1 !== 1'b1 && (MUX0_out !== MUX1_out)) |-> $isunknown(Y));

  // No-X on known select/data paths
  a_kn_00:   assert property ((S1===1'b0 && S0===1'b0 && !$isunknown(A)) |-> !$isunknown(Y));
  a_kn_01:   assert property ((S1===1'b0 && S0===1'b1 && !$isunknown(B)) |-> !$isunknown(Y));
  a_kn_10:   assert property ((S1===1'b1 && S0===1'b0 && !$isunknown(C)) |-> !$isunknown(Y));
  a_kn_11:   assert property ((S1===1'b1 && S0===1'b1 && !$isunknown(D)) |-> !$isunknown(Y));

  // Coverage: all select combos and X-propagation points
  c_00:      cover property (S1===1'b0 && S0===1'b0 && Y===A);
  c_01:      cover property (S1===1'b0 && S0===1'b1 && Y===B);
  c_10:      cover property (S1===1'b1 && S0===1'b0 && Y===C);
  c_11:      cover property (S1===1'b1 && S0===1'b1 && Y===D);

  c_s0x_m0:  cover property ((S0!==1'b0 && S0!==1'b1) && (A!==B) && $isunknown(MUX0_out));
  c_s0x_m1:  cover property ((S0!==1'b0 && S0!==1'b1) && (C!==D) && $isunknown(MUX1_out));
  c_s1x_y:   cover property ((S1!==1'b0 && S1!==1'b1) && (MUX0_out!==MUX1_out) && $isunknown(Y));

endmodule

bind MUX4 MUX4_sva mux4_sva_i();