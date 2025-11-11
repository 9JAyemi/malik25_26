// SVA checker for multiplier_block
// Focus: correctness, internal step checking, X-propagation, and key functional coverage.
// No clock/reset required; uses immediate assertions on combinational updates.

`ifndef SYNTHESIS
module multiplier_block_sva (
  input  logic [31:0] i_data0,
  input  logic [31:0] o_data0,
  input  logic [31:0] w1, w4, w16, w17, w13, w6656, w6643, w16384, w23027
);

  // Core functional correctness (mod 2^32)
  always_comb begin
    assert (o_data0 == (i_data0 * 32'd23027)[31:0])
      else $error("o_data0 != (i_data0 * 23027) mod 2^32");
  end

  // X/Z propagation: known input implies all outputs/nets known
  always_comb begin
    if (!$isunknown(i_data0)) begin
      assert (!$isunknown({o_data0,w1,w4,w16,w17,w13,w6656,w6643,w16384,w23027}))
        else $error("X/Z detected in internal/output with known input");
    end
  end

  // Structural step-by-step checks (catch width/sign mishaps)
  always_comb begin
    assert (w1      == i_data0)        else $error("w1 mismatch");
    assert (w4      == (w1 << 2))      else $error("w4 mismatch");
    assert (w16     == (w1 << 4))      else $error("w16 mismatch");
    assert (w16384  == (w1 << 14))     else $error("w16384 mismatch");
    assert (w17     == (w1 + w16))     else $error("w17 mismatch");
    assert (w13     == (w17 - w4))     else $error("w13 mismatch");
    assert (w6656   == (w13 << 9))     else $error("w6656 mismatch");
    assert (w6643   == (w6656 - w13))  else $error("w6643 mismatch");
    assert (w23027  == (w6643 + w16384)) else $error("w23027 mismatch");
    assert (o_data0 == w23027)         else $error("o_data0 != w23027");
  end

  // Algebraic invariants for each stage
  always_comb begin
    assert (w17    == (w1 * 32'd17)[31:0])     else $error("w17 != 17*w1 (mod 2^32)");
    assert (w13    == (w1 * 32'd13)[31:0])     else $error("w13 != 13*w1 (mod 2^32)");
    assert (w6656  == (w1 * 32'd6656)[31:0])   else $error("w6656 != 6656*w1 (mod 2^32)");
    assert (w6643  == (w1 * 32'd6643)[31:0])   else $error("w6643 != 6643*w1 (mod 2^32)");
    assert (w23027 == (w1 * 32'd23027)[31:0])  else $error("w23027 != 23027*w1 (mod 2^32)");
  end

  // Key functional coverage
  always_comb begin
    cover (i_data0 == 32'd0          && o_data0 == 32'd0);
    cover (i_data0 == 32'd1          && o_data0 == 32'd23027);
    cover (((i_data0 * 32'd23027) >> 32) != 0); // overflow observed
    cover (i_data0 == 32'hFFFF_FFFF  && o_data0 == 32'hFFFF_A60D);
  end

endmodule

// Bind into DUT; connects internal nets for full checking
bind multiplier_block multiplier_block_sva u_multiplier_block_sva (
  .i_data0 (i_data0),
  .o_data0 (o_data0),
  .w1      (w1),
  .w4      (w4),
  .w16     (w16),
  .w17     (w17),
  .w13     (w13),
  .w6656   (w6656),
  .w6643   (w6643),
  .w16384  (w16384),
  .w23027  (w23027)
);
`endif