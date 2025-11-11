// SVA checker for flt_fx. Bind this to the DUT instance.
// Focus: functional equivalence to spec, sign/zero/INF/NaN behavior,
// rounding behavior, overflow coverage, and combinational stability.

module flt_fx_sva
(
  input logic [31:0] fp_in,
  input logic [31:0] int_out
);

  // Reference model (bit-accurate to DUT)
  logic [47:0] ref_bias_mant;
  logic [7:0]  ref_bias_exp, ref_bias_exp2;
  logic [38:0] ref_ifo;     // intermediate fixed output before rounding
  logic [31:0] ref_fixed;   // rounded magnitude
  logic [31:0] ref_out;     // signed result

  always_comb begin
    ref_bias_mant = {25'h0001, fp_in[22:0]};
    ref_bias_exp  = fp_in[30:23] - 8'd127;
    ref_bias_exp2 = ~ref_bias_exp + 8'h1;

    if (fp_in[30:0] == 31'd0) begin
      ref_ifo = '0;
    end else if (ref_bias_exp[7]) begin
      ref_ifo = ref_bias_mant[38:0] >> ref_bias_exp2;
    end else begin
      ref_ifo = ref_bias_mant[38:0] << ref_bias_exp;
    end

    ref_fixed = ref_ifo[38:7] + ref_ifo[6];                // round to nearest (half-up)
    ref_out   = fp_in[31] ? (~ref_fixed + 32'd1) : ref_fixed;
  end

  // No X/Z on inputs/outputs
  always_comb begin
    assert (!$isunknown(fp_in))  else $error("flt_fx SVA: X/Z on fp_in");
    assert (!$isunknown(int_out)) else $error("flt_fx SVA: X/Z on int_out");
  end

  // Functional equivalence (core check)
  always_comb begin
    assert (int_out == ref_out)
      else $error("flt_fx SVA: mismatch fp_in=%h int_out=%h ref_out=%h", fp_in, int_out, ref_out);
  end

  // Zero, INF/NaN, and sign behavior
  always_comb begin
    // +0/-0 -> 0
    assert ((fp_in[30:0] == 31'd0) -> (int_out == 32'd0))
      else $error("flt_fx SVA: zero mapping failed fp_in=%h int_out=%h", fp_in, int_out);

    // exp==255 (INF/NaN) -> 0 per DUT behavior
    assert ((fp_in[30:23] == 8'hFF) -> (int_out == 32'd0))
      else $error("flt_fx SVA: INF/NaN should map to 0 fp_in=%h int_out=%h", fp_in, int_out);

    // Output sign consistent with input sign (except zero magnitude)
    assert ((fp_in[31] == 1'b0) -> (int_out[31] == 1'b0))
      else $error("flt_fx SVA: positive input produced negative int_out fp_in=%h int_out=%h", fp_in, int_out);

    assert ((fp_in[31] && (ref_fixed != 32'd0)) -> (int_out[31] == 1'b1))
      else $error("flt_fx SVA: negative input with nonzero magnitude did not produce negative int_out fp_in=%h int_out=%h", fp_in, int_out);
  end

  // Bias mantissa structure (only bit 23 is set in upper 25 bits)
  always_comb begin
    assert (ref_bias_mant[47:24] == 24'd0 && ref_bias_mant[23] == 1'b1)
      else $error("flt_fx SVA: bias_mant structure unexpected: %h", ref_bias_mant);
  end

  // Combinational stability: if input stable, output must not oscillate within the timestep
  property p_comb_stable;
    $stable(fp_in) |-> ##0 $stable(int_out);
  endproperty
  assert property (p_comb_stable)
    else $error("flt_fx SVA: int_out unstable for stable fp_in");

  // Coverage: exercise main paths and edge cases
  // Right-shift path (negative effective exponent, nonzero magnitude)
  cover property (fp_in[30:0] != 31'd0 && ref_bias_exp[7] == 1'b1);

  // Left-shift path (non-negative effective exponent, nonzero magnitude)
  cover property (fp_in[30:0] != 31'd0 && ref_bias_exp[7] == 1'b0);

  // Rounding down (round bit 0)
  cover property (fp_in[30:0] != 31'd0 && ref_ifo[6] == 1'b0);

  // Rounding up (round bit 1)
  cover property (fp_in[30:0] != 31'd0 && ref_ifo[6] == 1'b1);

  // Left-shift overflow potential (exp >= 16 moves the implicit 1 past bit 38)
  cover property (fp_in[30:0] != 31'd0 && ref_bias_exp[7] == 1'b0 && ref_bias_exp >= 8'd16);

  // Subnormal (exp==0, frac!=0)
  cover property (fp_in[30:23] == 8'd0 && fp_in[22:0] != 23'd0);

  // +0 and -0
  cover property (fp_in == 32'h0000_0000 && int_out == 32'd0);
  cover property (fp_in == 32'h8000_0000 && int_out == 32'd0);

  // INF and NaN
  cover property (fp_in[30:23] == 8'hFF && fp_in[22:0] == 23'd0 && int_out == 32'd0); // INF
  cover property (fp_in[30:23] == 8'hFF && fp_in[22:0] != 23'd0 && int_out == 32'd0); // NaN

  // Negative input that rounds to zero
  cover property (fp_in[31] && fp_in[30:0] != 31'd0 && int_out == 32'd0);

endmodule

// Bind into every flt_fx instance. If you have a hierarchy path, you can also bind to a specific instance.
bind flt_fx flt_fx_sva i_flt_fx_sva (.fp_in(fp_in), .int_out(int_out));