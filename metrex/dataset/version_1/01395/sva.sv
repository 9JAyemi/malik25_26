// SVA bind for top_module: concise, high-quality checks and coverage
bind top_module top_module_sva();

module top_module_sva;

  // Signed lane slices
  wire signed [7:0] a0 = a[7:0];
  wire signed [7:0] a1 = a[15:8];
  wire signed [7:0] a2 = a[23:16];
  wire signed [7:0] a3 = a[31:24];
  wire signed [7:0] b0 = b[7:0];
  wire signed [7:0] b1 = b[15:8];
  wire signed [7:0] b2 = b[23:16];
  wire signed [7:0] b3 = b[31:24];

  // Expected lane results
  wire signed [15:0] e0 = a0 * b0;
  wire signed [15:0] e1 = a1 * b1;
  wire signed [15:0] e2 = a2 * b2;
  wire signed [15:0] e3 = a3 * b3;

  // Combinational assertions and coverage
  always_comb begin
    // Structural passthrough (no storage)
    assert (stage1_reg === stage1_out) else $error("stage1_reg != stage1_out");
    assert (stage2_reg === stage2_out) else $error("stage2_reg != stage2_out");
    assert (stage3_reg === stage3_out) else $error("stage3_reg != stage3_out");
    assert (stage4_reg === stage4_out) else $error("stage4_reg != stage4_out");

    // Product concatenation mapping
    assert (product === {stage4_reg,stage3_reg,stage2_reg,stage1_reg})
      else $error("product concat != stage regs");

    // Arithmetic correctness (when inputs known)
    if (!$isunknown({a,b})) begin
      assert (stage1_out == e0) else $error("lane0 mult mismatch");
      assert (stage2_out == e1) else $error("lane1 mult mismatch");
      assert (stage3_out == e2) else $error("lane2 mult mismatch");
      assert (stage4_out == e3) else $error("lane3 mult mismatch");

      assert (product == {e3,e2,e1,e0})
        else $error("product != expected concatenated lane multiplies");

      // Zero-result rule per lane
      if (a0 == 0 || b0 == 0) assert (stage1_out == 0) else $error("lane0 zero rule");
      if (a1 == 0 || b1 == 0) assert (stage2_out == 0) else $error("lane1 zero rule");
      if (a2 == 0 || b2 == 0) assert (stage3_out == 0) else $error("lane2 zero rule");
      if (a3 == 0 || b3 == 0) assert (stage4_out == 0) else $error("lane3 zero rule");

      // Sign correctness when nonzero (no overflow in 8x8->16)
      if (a0 != 0 && b0 != 0) assert (stage1_out[15] == (a0[7] ^ b0[7])) else $error("lane0 sign rule");
      if (a1 != 0 && b1 != 0) assert (stage2_out[15] == (a1[7] ^ b1[7])) else $error("lane1 sign rule");
      if (a2 != 0 && b2 != 0) assert (stage3_out[15] == (a2[7] ^ b2[7])) else $error("lane2 sign rule");
      if (a3 != 0 && b3 != 0) assert (stage4_out[15] == (a3[7] ^ b3[7])) else $error("lane3 sign rule");

      // No X/Z on outputs when inputs are known
      assert (!$isunknown({stage1_out,stage2_out,stage3_out,stage4_out,
                           stage1_reg,stage2_reg,stage3_reg,stage4_reg,product}))
        else $error("X/Z detected on outputs with known inputs");
    end

    // Functional coverage (immediate covers for key corners and mixes)
    cover (e0 == 0 && e1 == 0 && e2 == 0 && e3 == 0);                           // all zero
    cover (e0 > 0 && e1 < 0 && e2 > 0 && e3 < 0);                               // mixed signs
    cover (e0 < 0 && e1 > 0 && e2 < 0 && e3 > 0);                               // mixed signs alt
    cover (e0 == 16'sd16129);                                                   // 127*127
    cover (e0 == 16'sd16384);                                                   // -128*-128
    cover (e0 == -16'sd16256);                                                  // -128*127
    cover (product[15:0] == 0 && product[63:48] != 0);                          // cross-lane diversity
  end

endmodule