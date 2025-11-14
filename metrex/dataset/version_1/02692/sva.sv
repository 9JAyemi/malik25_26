// SVA for binary_multiplier
// Bind this to the DUT. Focus: functional correctness, sign, X-prop, internal consistency, targeted coverage.

module binary_multiplier_sva (
  input logic [3:0] a, b,
  input logic [7:0] p,
  input logic       sign,
  input logic [7:0] temp_p,
  input logic       a_sign, b_sign, p_sign
);

  // Canonical signed extensions and products
  let a_s        = $signed({{4{a[3]}}, a});        // 8-bit signed
  let b_s        = $signed({{4{b[3]}}, b});        // 8-bit signed
  let prod16     = a_s * b_s;                      // 16-bit signed
  let absA       = a_s[7] ? -a_s : a_s;            // 8-bit signed magnitude
  let absB       = b_s[7] ? -b_s : b_s;            // 8-bit signed magnitude
  let absProd16  = absA * absB;                    // 16-bit magnitude product

  // Combinational safety and functional checks
  always_comb begin
    // No X/Z on inputs; no X/Z on outputs/internals when inputs are known
    assert (!$isunknown({a,b})) else $error("Inputs contain X/Z");
    if (!$isunknown({a,b})) begin
      assert (!$isunknown({p,sign,temp_p,a_sign,b_sign,p_sign}))
        else $error("Outputs/internal contain X/Z with clean inputs");
    end

    // Internal sign wires consistent with interface and operands
    assert (a_sign == a[3] && b_sign == b[3]) else $error("a_sign/b_sign mismatch");
    assert (p_sign == (a_sign ^ b_sign)) else $error("p_sign != a_sign^b_sign");

    // Sign bit equals MSB of product; zero result must have sign=0
    assert (sign == p[7]) else $error("sign != p[7]");
    if ((a != 4'd0) && (b != 4'd0))
      assert (sign == (a[3]^b[3])) else $error("nonzero result sign mismatch");
    if ((a == 4'd0) || (b == 4'd0)) begin
      assert (p == 8'd0) else $error("zero operand should yield p=0");
      assert (sign == 1'b0) else $error("zero product must have sign=0");
      assert (temp_p == 8'd0) else $error("temp_p must be 0 for zero operand");
    end

    // Golden functional spec: full signed product
    assert ($signed(p) == prod16[7:0]) else $error("p != signed(a)*signed(b)");

    // Implementation consistency: 2's complement of magnitude when negative
    assert (p == (p_sign ? (~temp_p + 8'd1) : temp_p))
      else $error("p not consistent with p_sign/temp_p two's complement");

    // Magnitude path must equal |a|*|b|
    assert (temp_p == absProd16[7:0]) else $error("temp_p != |a|*|b|");
  end

  // Targeted functional coverage
  // Quadrants and key corners
  cover property (a == 4'd0 && b == 4'd0 && p == 8'd0 && sign == 1'b0);
  cover property (a != 4'd0 && b == 4'd0 && p == 8'd0);
  cover property (a == 4'd0 && b != 4'd0 && p == 8'd0);

  cover property (!a[3] && !b[3] && p[7] == 1'b0 && p != 8'd0); // + * +
  cover property ( a[3] &&  b[3] && p[7] == 1'b0 && p != 8'd0); // - * -
  cover property ( a[3] && !b[3] && p[7] == 1'b1 && p != 8'd0); // - * +
  cover property (!a[3] &&  b[3] && p[7] == 1'b1 && p != 8'd0); // + * -

  // Extremes and sanity points
  cover property ($signed(a_s) == -8 && $signed(b_s) == -8 && $signed(p) == 8'sd64);
  cover property ($signed(a_s) ==  7 && $signed(b_s) ==  7 && $signed(p) == 8'sd49);
  cover property ($signed(a_s) == -8 && $signed(b_s) ==  7 && $signed(p) == -8'sd56);
  cover property ($signed(a_s) == -1 && $signed(b_s) == -1 && $signed(p) == 8'sd1);

endmodule

// Bind into DUT (tools allow binding to internal nets/wires)
bind binary_multiplier binary_multiplier_sva sva_i (
  .a(a), .b(b), .p(p), .sign(sign),
  .temp_p(temp_p), .a_sign(a_sign), .b_sign(b_sign), .p_sign(p_sign)
);