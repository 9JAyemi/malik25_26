// SVA binders for adder16 and full_adder

// Bind into adder16 to check word-level correctness, ripple-carry structure, X-prop, and key coverage
module adder16_sva;
  // helper: 17-bit add
  function automatic logic [16:0] add17(input logic [15:0] aa, input logic [15:0] bb, input logic cc);
    add17 = {1'b0,aa} + {1'b0,bb} + cc;
  endfunction

  // helper: carry-in to bit idx (0..16), recomputed from inputs
  function automatic logic carry_in_to(input int idx, input logic [15:0] aa, input logic [15:0] bb, input logic cc);
    logic c;
    c = cc;
    for (int k = 0; k < idx; k++) begin
      c = (aa[k] & bb[k]) | ((aa[k] ^ bb[k]) & c);
    end
    return c;
  endfunction

  always_comb begin
    // X/Z propagation: known inputs must yield known outputs
    if (!$isunknown({a,b,cin})) begin
      assert (!$isunknown({sum,cout})) else $error("adder16: X/Z on outputs with known inputs");
    end

    // Word-level equivalence
    assert ({cout,sum} == add17(a,b,cin)) else $error("adder16: word-level mismatch");

    // Structural/ripple checks
    assert (carry[0] == cin) else $error("adder16: carry[0] mismatch");
    assert (cout == carry[15]) else $error("adder16: cout connectivity mismatch");
    assert (sum[0] == (a[0] ^ b[0] ^ cin)) else $error("adder16: sum[0] mismatch");

    for (int i = 1; i < 16; i++) begin
      assert (carry[i] == ((a[i] & b[i]) | ((a[i] ^ b[i]) & carry[i-1])))
        else $error("adder16: carry[%0d] mismatch", i);
      assert (sum[i] == (a[i] ^ b[i] ^ carry[i-1]))
        else $error("adder16: sum[%0d] mismatch", i);
    end

    // Independent recomputation cross-check
    for (int i = 1; i < 16; i++) begin
      logic cin_i = carry_in_to(i, a, b, cin);
      assert (sum[i] == (a[i] ^ b[i] ^ cin_i))
        else $error("adder16: sum[%0d] mismatch vs recomputed carry_in", i);
    end
    assert (cout == carry_in_to(16, a, b, cin))
      else $error("adder16: cout mismatch vs recomputed carry_in");
  end

  // Functional coverage for important scenarios
  always_comb begin
    cover (cin == 0);
    cover (cin == 1);
    cover (cout == 1);
    cover (sum == 16'h0000);
    cover (sum == 16'hFFFF);
    // Long ripple carry through all bits
    cover (a == 16'hFFFF && b == 16'h0001 && cin == 1'b0 && sum == 16'h0000 && cout == 1'b1);
    // MSB generate case
    cover (a[15] && b[15] && !cin && cout && sum[15] == 1'b0);
    // Per-bit generate / propagate-capable / kill
    for (int i = 0; i < 16; i++) begin
      cover (a[i] & b[i]);     // generate
      cover (a[i] ^ b[i]);     // propagate-capable
      cover (~a[i] & ~b[i]);   // kill
    end
  end
endmodule

bind adder16 adder16_sva sva_adder16();

// Bind into full_adder for local correctness and X-prop
module full_adder_sva;
  always_comb begin
    if (!$isunknown({a,b,cin})) assert (!$isunknown({sum,cout})) else $error("full_adder: X/Z on outputs with known inputs");
    assert (sum == (a ^ b ^ cin)) else $error("full_adder: sum mismatch");
    assert (cout == ((a & b) | (a & cin) | (b & cin))) else $error("full_adder: cout mismatch");
  end

  // Simple local coverage
  always_comb begin
    cover (a ^ b);   // propagate-capable
    cover (a & b);   // generate
    cover (cin);     // carry-in asserted
  end
endmodule

bind full_adder full_adder_sva sva_full_adder();