// SVA for mux17
// Bind this checker to the DUT instance to verify combinational mux behavior.
// Focus: correctness, X-checks, and concise functional coverage.
// synthesis translate_off

module mux17_sva (
  input logic [16:0] A,
  input logic [16:0] B,
  input logic        S,
  input logic [16:0] MO
);

  // Core functional equivalence (bit-accurate, 4-state)
  always_comb begin
    assert (MO === (S ? B : A))
      else $error("mux17: MO != (S?B:A)");
  end

  // Select must be known 0/1
  always_comb begin
    assert (!$isunknown(S))
      else $error("mux17: S is X/Z");
  end

  // Deterministic known-ness: if select and chosen input are known, MO must be known
  always_comb begin
    if (S === 1'b0 && !$isunknown(A)) assert (!$isunknown(MO)) else $error("mux17: MO unknown with S=0 and A known");
    if (S === 1'b1 && !$isunknown(B)) assert (!$isunknown(MO)) else $error("mux17: MO unknown with S=1 and B known");
  end

  // Concurrent assertions per select value (redundant to core check, but clearer intent)
  property p_sel0;  @(*) (S === 1'b0) |-> (MO === A); endproperty
  property p_sel1;  @(*) (S === 1'b1) |-> (MO === B); endproperty
  assert property (p_sel0) else $error("mux17: S=0 but MO!=A");
  assert property (p_sel1) else $error("mux17: S=1 but MO!=B");

  // Minimal, meaningful coverage: both paths and edge-triggered checks
  cover property (@(*) (S === 1'b0 && MO === A));
  cover property (@(*) (S === 1'b1 && MO === B));
  cover property (@(negedge S) (MO === A));
  cover property (@(posedge S) (MO === B));

  // Exercise non-trivial path choices when inputs differ
  cover property (@(*) (S === 1'b0 && (A !== B) && MO === A));
  cover property (@(*) (S === 1'b1 && (A !== B) && MO === B));

endmodule

// Bind to the DUT
bind mux17 mux17_sva mux17_sva_i (.A(A), .B(B), .S(S), .MO(MO));

// synthesis translate_on