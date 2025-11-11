// SVA for mux_2to1
module mux_2to1_sva (
  input  logic [15:0] A,
  input  logic [15:0] B,
  input  logic        S,
  input  logic [15:0] MO
);

  // Functional equivalence (4-state accurate)
  assert property (@(*) MO === ((S == 1'b1) ? B : A));

  // Deterministic select mapping when S is known
  assert property (@(*) (S === 1'b0) |-> (MO === A));
  assert property (@(*) (S === 1'b1) |-> (MO === B));

  // No spurious output change without any input change
  assert property (@(*) $changed(MO) |-> $changed({A,B,S}));

  // Knownness when selected data is known
  assert property (@(*) (S === 1'b0 && !$isunknown(A)) |-> (!$isunknown(MO) && MO === A));
  assert property (@(*) (S === 1'b1 && !$isunknown(B)) |-> (!$isunknown(MO) && MO === B));

  // Coverage: both select directions with meaningful data
  cover property (@(*) (S === 1'b0) && (A != B) && (MO === A));
  cover property (@(*) (S === 1'b1) && (A != B) && (MO === B));

  // Coverage: select toggles
  cover property (@(posedge S));
  cover property (@(negedge S));

  // Coverage: unknown select with differing data propagates Xs
  cover property (@(*) (S !== 1'b0 && S !== 1'b1) && ((A ^ B) != 16'b0) && $isunknown(MO));

  // Coverage: unknown select with equal data yields stable output
  cover property (@(*) (S !== 1'b0 && S !== 1'b1) && (A === B) && (MO === A));

endmodule

// Bind into DUT
bind mux_2to1 mux_2to1_sva i_mux_2to1_sva (.*);