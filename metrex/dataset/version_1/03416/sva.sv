// SVA bind file for EnergyHarvestingBlock
// Checks arithmetic correctness, widths, divide-by-zero, and key coverage.
// Bind into the DUT to access internals (v,i,p,w).

module EnergyHarvestingBlock_sva;

  // Wide recompute to avoid truncation during checking
  logic [63:0] e_u;
  logic [63:0] v_exp, i_exp, p_exp, w_exp, q_exp;
  logic [63:0] denom1, denom2;

  // Static/parameter checks
  initial begin
    assert (n > 0) else $error("n must be > 0");
    assert (voltage >= 0 && current >= 0) else $error("voltage/current must be >= 0");
    assert ((1000*n) != 0) else $error("Final denominator 1000*n is zero");
  end

  // Recompute expected values in wide precision
  always_comb begin
    e_u    = e;
    v_exp  = logic'(64'(voltage)) * e_u;
    i_exp  = logic'(64'(current)) * e_u;
    denom1 = v_exp + i_exp;
    p_exp  = (v_exp * i_exp) / 1000;
    w_exp  = (denom1 != 0) ? (p_exp * 1000) / denom1 : 64'hX;
    denom2 = 1000 * n;
    q_exp  = (denom2 != 0) ? (w_exp * v_exp) / denom2 : 64'hX; // quotient before trunc to 1b
  end

  // Input/X checks and arithmetic safety
  always_comb begin
    assert (!$isunknown(e)) else $error("Input e contains X/Z");
    assert (denom1 != 0) else $error("Divide-by-zero in w: v+i==0 (e==0)");
  end

  // Width/overflow protection (no silent truncation)
  always_comb begin
    assert (v_exp <= 16'hFFFF) else $error("v overflows 16 bits");
    assert (i_exp <= 16'hFFFF) else $error("i overflows 16 bits");
    assert (p_exp <= 32'hFFFF_FFFF) else $error("p overflows 32 bits");
    assert (w_exp <= 32'hFFFF_FFFF) else $error("w overflows 32 bits");
  end

  // Functional equivalence of all internal computations
  always_comb begin
    assert (v == v_exp[15:0])          else $error("v mismatch");
    assert (i == i_exp[15:0])          else $error("i mismatch");
    assert (p == p_exp[31:0])          else $error("p mismatch");
    assert (w == w_exp[31:0])          else $error("w mismatch");
    // out is a 1-bit net; it must equal LSB of the integer quotient
    assert (out === q_exp[0])          else $error("out mismatch (LSB of (w*v)/(1000*n))");
  end

  // Targeted coverage
  // - Stimulus edges: zero, single-source (LSB, MSB), and all-on
  // - Output both 0 and 1, and odd/even quotient cases
  always_comb begin
    cover (e == {n{1'b0}});                      // all off (illegal for div; still useful to observe)
    cover (e == logic [n-1:0]'(1));              // only LSB on
    cover (e == (logic [n-1:0]'(1) << (n-1)));   // only MSB on
    cover (e == {n{1'b1}});                      // all on

    cover (out == 1'b0);
    cover (out == 1'b1);

    if (denom1 != 0) begin
      cover (q_exp == 0);            // quotient zero
      cover (q_exp[0] == 1'b1);      // quotient odd -> out should be 1
      cover (q_exp[0] == 1'b0);      // quotient even -> out should be 0
    end
  end

endmodule

bind EnergyHarvestingBlock EnergyHarvestingBlock_sva;