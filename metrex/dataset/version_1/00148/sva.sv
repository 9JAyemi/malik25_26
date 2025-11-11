// SVA for FpuFp64FromInt
// Concise checks for key behaviors, normalization, and corner cases.
// Bind into the DUT scope to access internal regs.

module FpuFp64FromInt_sva;
  // Inherit DUT signals by hierarchical reference via bind
  default clocking cb @(posedge clk); endclocking

  // Helper: source sign bit based on is32
  function automatic bit src_sign_f();
    return is32 ? src[31] : src[63];
  endfunction

  // Outputs must not change when enable is low
  property p_stable_when_disabled;
    !enable |-> $stable(dst);
  endproperty
  assert property(p_stable_when_disabled);

  // Exponent base must be constant (1023 + 52 = 1075)
  assert property (enable |-> exm == 13'd1075);

  // For 32-bit mode, pre-extend should zero the upper 32 bits of tFracC2
  assert property (enable && is32 |-> ##[0:1] (tFracC2[63:32] == 32'h0));

  // Zero input must yield +0.0
  assert property (enable && ( (is32 && (src[31:0]==32'h0)) || (!is32 && (src==64'h0)) )
                   |-> ##[0:1] (dst == 64'h0));

  // Underflow flag path drives exact zero
  assert property (enable && exc[12] |-> ##[0:1] (dst == 64'h0));

  // Overflow flag path drives infinity with the module’s sign bit (sgnc)
  assert property (enable && !exc[12] && exc[11]
                   |-> ##[0:1] (dst == {sgnc, 11'h7FF, 52'h0}));

  // Zero-detect consistency: if magnitude is zero then fraction/exponent cleared
  assert property (enable && (tFracC2[52:0] == 53'h0) |-> (tFracC == 64'h0 && exc == 13'h0));

  // Normalized non-zero results: fraction MSB must be 1 and fields must map to dst
  assert property (enable && !exc[12] && !exc[11] && (tFracC != 64'h0)
                   |-> ##[0:1] (tFracC[52] && dst[62:52]==exc[10:0] && dst[51:0]==tFracC[51:0] && dst[63]==sgnc));

  // Sign must follow input sign on non-zero conversions (intended behavior)
  // This will flag mismatch if sgnc is not wired to src sign.
  assert property (enable && ( (is32 && (src[31:0]!=0)) || (!is32 && (src!=0)) )
                   |-> ##[0:1] (dst[63] == src_sign_f()));

  // ------------- Coverage -------------

  // Exercise 32-bit paths
  cover property (enable && is32 && (src[31:0]==32'h0));            // 32-bit zero
  cover property (enable && is32 && src[31]);                       // 32-bit negative
  cover property (enable && is32 && !src[31] && (src[30:0]!=0));    // 32-bit positive non-zero

  // Exercise 64-bit paths
  cover property (enable && !is32 && (src==64'h0));                 // 64-bit zero
  cover property (enable && !is32 && src[63]);                      // 64-bit negative
  cover property (enable && !is32 && !src[63] && (src[62:0]!=0));   // 64-bit positive non-zero

  // Normalization corner cases
  cover property (enable && (tFracC2[63:60]!=0));                   // Right-shift normalization (large magnitude)
  cover property (enable && (tFracC2[52:21]==0) && (tFracC2[52:0]!=0)); // Large left-shift normalization
  cover property (enable && !exc[12] && !exc[11] && (tFracC!=0) && tFracC[52]); // Normalized non-zero

  // Exceptional results
  cover property (enable && exc[11]); // Infinity
  cover property (enable && exc[12]); // Underflow to zero
endmodule

bind FpuFp64FromInt FpuFp64FromInt_sva sva_inst();