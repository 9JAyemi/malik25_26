// SVA for carry_lookahead_adder + overflow_detector + top_module
// Concise, combinational immediate assertions with bind

// Assertions for the CLA: independently recompute carries and sum
module cla_add_sva (
  input  logic [7:0] a,
  input  logic [7:0] b,
  input  logic [7:0] s,
  input  logic       carry_out,
  input  logic [7:0] p,
  input  logic [7:0] g,
  input  logic [7:0] c
);
  logic [7:0] r;      // independent ripple carry (carry into bit i+1)
  logic [8:0] expsum; // golden 9-bit sum

  always_comb begin
    // basic generate/propagate correctness
    assert (p == (a ^ b)) else $error("CLA p mismatch");
    assert (g == (a & b)) else $error("CLA g mismatch");

    // independent carry recomputation
    r[0] = g[0];
    foreach (r[i]) if (i>0) r[i] = g[i] | (p[i] & r[i-1]);
    assert (c == r) else $error("CLA carry vector mismatch");
    assert (carry_out == r[7]) else $error("CLA carry_out mismatch");

    // bitwise sum (sum[i] = p[i] ^ carry_in_to_bit_i)
    assert (s[0] == p[0]) else $error("CLA s[0] mismatch");
    for (int i=1; i<8; i++) assert (s[i] == (p[i] ^ r[i-1])) else $error("CLA s[%0d] mismatch", i);

    // numeric sum equivalence
    expsum = a + b;
    assert ({carry_out, s} == expsum) else $error("CLA sum mismatch: %0h + %0h", a, b);

    // no X/Z on outputs when inputs are known
    if (!$isunknown({a,b})) assert (!$isunknown({s,carry_out,p,g,c})) else $error("CLA outputs unknown for known inputs");

    // coverage
    cover (carry_out);
    cover (s == 8'h00);
    cover (s == 8'hFF);
    cover (a == 8'h7F && b == 8'h01); // positive overflow stimulus
    cover (a == 8'h80 && b == 8'h80); // negative overflow stimulus
  end
endmodule

bind carry_lookahead_adder cla_add_sva cla_add_sva_i (
  .a(a), .b(b), .s(s), .carry_out(carry_out),
  .p(p), .g(g), .c(c)
);

// Assertions for overflow_detector: logical equivalences
module ovf_sva (
  input  logic [7:0] a,
  input  logic [7:0] b,
  input  logic [7:0] s,
  input  logic       overflow
);
  always_comb begin
    // primary definition
    assert (overflow == ((a[7] == b[7]) && (a[7] != s[7])))
      else $error("OVF mismatch (sign rule)");

    // equivalent canonical form
    assert (overflow == (( a[7] &  b[7] & ~s[7]) | (~a[7] & ~b[7] &  s[7])))
      else $error("OVF mismatch (canonical)");

    // coverage of both overflow polarities
    cover (a[7]==0 && b[7]==0 && s[7]==1 && overflow);
    cover (a[7]==1 && b[7]==1 && s[7]==0 && overflow);

    if (!$isunknown({a,b,s})) assert (!overflow || (a[7]==b[7])) else $error("OVF asserted with opposite-sign inputs");
  end
endmodule

bind overflow_detector ovf_sva ovf_sva_i (.a(a), .b(b), .s(s), .overflow(overflow));

// Cross-module consistency at top: overflow vs carries, and sum
module top_sva (
  input  logic [7:0] a,
  input  logic [7:0] b,
  input  logic [7:0] s,
  input  logic       overflow,
  input  logic       ci7,   // carry into MSB (bit7): adder.c[6]
  input  logic       co7    // carry out of MSB:     adder.c[7]
);
  always_comb begin
    // consistent numeric sum at top-level
    assert ({co7, s} == (a + b)) else $error("TOP sum mismatch");

    // overflow equals carry into MSB xor carry out of MSB
    assert (overflow == (ci7 ^ co7)) else $error("TOP overflow vs carries mismatch");

    cover (overflow);
    cover (co7);
  end
endmodule

bind top_module top_sva top_sva_i (
  .a(a), .b(b), .s(s), .overflow(overflow),
  .ci7(adder.c[6]), .co7(adder.c[7])
);