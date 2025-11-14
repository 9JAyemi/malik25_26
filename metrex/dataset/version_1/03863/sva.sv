// SVA for DBLC_3_64
// Checks exact functionality and basic coverage. Purely combinational checks use immediate assertions.

module DBLC_3_64_sva (
  input  [0:62] PIN,
  input  [0:64] GIN,
  input         PHI,
  input  [0:60] POUT,
  input  [0:64] GOUT
);

  bit seen_phi0, seen_phi1;

  // Continuous functional correctness
  always_comb begin
    // GOUT mirrors GIN bit-for-bit (including X/Z)
    assert (GOUT === GIN)
      else $error("DBLC_3_64: GOUT must mirror GIN");

    // POUT selects slice [62:2] from GIN or PIN per PHI (including X/Z semantics)
    assert (POUT === (PHI ? GIN[62:2] : PIN[62:2]))
      else $error("DBLC_3_64: POUT mismatch with selected slice");

    // Knownness propagation (no spurious X on outputs when controlling inputs are known)
    if (!$isunknown(GIN))    assert (!$isunknown(GOUT)) else $error("DBLC_3_64: GOUT unknown while GIN known");
    if (!$isunknown(PHI)) begin
      if (PHI==1'b1 && !$isunknown(GIN[62:2]))
        assert (!$isunknown(POUT)) else $error("DBLC_3_64: POUT unknown while PHI=1 and GIN[62:2] known");
      if (PHI==1'b0 && !$isunknown(PIN[62:2]))
        assert (!$isunknown(POUT)) else $error("DBLC_3_64: POUT unknown while PHI=0 and PIN[62:2] known");
    end

    // Lightweight functional coverage
    cover (GOUT === GIN);
    if (PHI==1'b0) begin
      seen_phi0 = 1'b1;
      cover (POUT === PIN[62:2]);
    end
    if (PHI==1'b1) begin
      seen_phi1 = 1'b1;
      cover (POUT === GIN[62:2]);
    end
  end

  // Ensure both selection branches were observed
  final begin
    assert (seen_phi0) else $warning("DBLC_3_64: PHI=0 branch never observed");
    assert (seen_phi1) else $warning("DBLC_3_64: PHI=1 branch never observed");
  end

endmodule

bind DBLC_3_64 DBLC_3_64_sva u_dblc_3_64_sva (
  .PIN  (PIN),
  .GIN  (GIN),
  .PHI  (PHI),
  .POUT (POUT),
  .GOUT (GOUT)
);