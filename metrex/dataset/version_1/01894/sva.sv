// SVA for JNOR3C
// Bind into the DUT to access internal nets directly.
module JNOR3C_sva;

  // Structural correctness of internal nets and final output
  always_comb begin
    // Unknown/X checks: with known inputs, all derived nets must be known
    if (!$isunknown({A1,A2,A3,A4})) begin
      assert (!$isunknown({M1,M2,M3,N1,N2,O})) else $error("JNOR3C: X/Z on internal/output with known inputs");
    end

    // Internal equations
    assert (M1 == (A1 & A2)) else $error("JNOR3C: M1 != A1&A2");
    assert (M2 == (A2 & A3)) else $error("JNOR3C: M2 != A2&A3");
    assert (M3 == (A1 & A3)) else $error("JNOR3C: M3 != A1&A3");
    assert (N1 == ~(M1 | M2)) else $error("JNOR3C: N1 != ~(M1|M2)");
    assert (N2 == ~(M1 | M3)) else $error("JNOR3C: N2 != ~(M1|M3)");

    // Output equations (original and simplified cross-check)
    assert (O  == ~(N1 | N2 | (A1 & A2 & A3 & A4))) else $error("JNOR3C: O original equation mismatch");
    assert (O  == ((A1 & A2) & !(A3 & A4)))       else $error("JNOR3C: O simplified equation mismatch");

    // Directional sanity
    if (O)                             assert (A1 && A2) else $error("JNOR3C: O=1 requires A1&A2=1");
    if (A1 && A2 && A3 && A4)          assert (!O)       else $error("JNOR3C: O must be 0 when A1&A2&A3&A4=1");
    if (!(A1 && A2))                   assert (!O)       else $error("JNOR3C: O must be 0 unless A1&A2=1");
  end

  // Functional coverage of key corners
  always_comb begin
    cover (O);
    cover (!O);
    cover (A1 && A2 && !A3 &&  A4 && O); // O due to !A3
    cover (A1 && A2 &&  A3 && !A4 && O); // O due to !A4
    cover (A1 && A2 &&  A3 &&  A4 && !O); // 4-way AND blocks O
    cover ( A1 && !A2 && !O);
    cover (!A1 &&  A2 && !O);
  end

endmodule

bind JNOR3C JNOR3C_sva jnor3c_sva_i();