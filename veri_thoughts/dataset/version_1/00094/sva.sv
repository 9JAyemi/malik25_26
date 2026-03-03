// SVA bind file for FullAdder and RippleAdder2
// Focused, high-quality checks plus concise coverage

module FullAdder_sva #(parameter bit ENABLE_COV=1)
(
  input logic a, b, ci,
  input logic co, s
);
  always_comb begin
    // No X/Z
    assert (!$isunknown({a,b,ci})) else $error("%m X/Z on inputs");
    assert (!$isunknown({co,s}))   else $error("%m X/Z on outputs");

    // Functional correctness
    assert ({co,s} == a + b + ci)
      else $error("%m sum mismatch: a=%0b b=%0b ci=%0b -> co,s=%0b%0b", a,b,ci,co,s);
    assert (co == ((a & b) | (a & ci) | (b & ci)))
      else $error("%m carry equation mismatch");
    assert (s == (a ^ b ^ ci))
      else $error("%m sum-bit equation mismatch");

    // Compact truth-table coverage
    if (ENABLE_COV) begin
      cover ({a,b,ci} == 3'b000);
      cover ({a,b,ci} == 3'b001);
      cover ({a,b,ci} == 3'b010);
      cover ({a,b,ci} == 3'b011);
      cover ({a,b,ci} == 3'b100);
      cover ({a,b,ci} == 3'b101);
      cover ({a,b,ci} == 3'b110);
      cover ({a,b,ci} == 3'b111);
      cover (co);   // carry seen
      cover (!co);  // no carry
    end
  end
endmodule

module RippleAdder2_sva #(parameter bit ENABLE_COV=1)
(
  input logic [3:0] a, b,
  input logic ci,
  input logic co,
  input logic [3:0] s,

  // observe internals
  input logic [4:0] c,
  input logic sig_fa_0_a, sig_fa_0_b, sig_fa_0_ci, sig_fa_0_co, sig_fa_0_s,
  input logic sig_fa_1_a, sig_fa_1_b, sig_fa_1_ci, sig_fa_1_co, sig_fa_1_s,
  input logic sig_fa_2_a, sig_fa_2_b, sig_fa_2_ci, sig_fa_2_co, sig_fa_2_s,
  input logic sig_fa_3_a, sig_fa_3_b, sig_fa_3_ci, sig_fa_3_co, sig_fa_3_s
);
  always_comb begin
    // No X/Z anywhere important
    assert (!$isunknown({a,b,ci,co,s,c,
                         sig_fa_0_a,sig_fa_0_b,sig_fa_0_ci,sig_fa_0_co,sig_fa_0_s,
                         sig_fa_1_a,sig_fa_1_b,sig_fa_1_ci,sig_fa_1_co,sig_fa_1_s,
                         sig_fa_2_a,sig_fa_2_b,sig_fa_2_ci,sig_fa_2_co,sig_fa_2_s,
                         sig_fa_3_a,sig_fa_3_b,sig_fa_3_ci,sig_fa_3_co,sig_fa_3_s}))
      else $error("%m X/Z detected");

    // Top-level spec
    assert ({co,s} == a + b + ci)
      else $error("%m {co,s} != a+b+ci");

    // Carry chain assembly and output mapping
    assert (c[0] == ci)           else $error("%m c[0]!=ci");
    assert (c[1] == sig_fa_0_co)  else $error("%m c[1]!=fa0.co");
    assert (c[2] == sig_fa_1_co)  else $error("%m c[2]!=fa1.co");
    assert (c[3] == sig_fa_2_co)  else $error("%m c[3]!=fa2.co");
    assert (c[4] == sig_fa_3_co)  else $error("%m c[4]!=fa3.co");
    assert (co   == c[4])         else $error("%m co!=c[4]");

    // Stage input wiring
    assert (sig_fa_0_a == a[0])   else $error("%m fa0.a!=a[0]");
    assert (sig_fa_0_b == b[0])   else $error("%m fa0.b!=b[0]");
    assert (sig_fa_0_ci == c[0])  else $error("%m fa0.ci!=c[0]");

    assert (sig_fa_1_a == a[1])   else $error("%m fa1.a!=a[1]");
    assert (sig_fa_1_b == b[1])   else $error("%m fa1.b!=b[1]");
    assert (sig_fa_1_ci == c[1])  else $error("%m fa1.ci!=c[1]");

    assert (sig_fa_2_a == a[2])   else $error("%m fa2.a!=a[2]");
    assert (sig_fa_2_b == b[2])   else $error("%m fa2.b!=b[2]");
    assert (sig_fa_2_ci == c[2])  else $error("%m fa2.ci!=c[2]");

    assert (sig_fa_3_a == a[3])   else $error("%m fa3.a!=a[3]");
    assert (sig_fa_3_b == b[3])   else $error("%m fa3.b!=b[3]");
    assert (sig_fa_3_ci == c[3])  else $error("%m fa3.ci!=c[3]");

    // Stage functionality
    assert ({sig_fa_0_co, sig_fa_0_s} == sig_fa_0_a + sig_fa_0_b + sig_fa_0_ci)
      else $error("%m fa0 sum mismatch");
    assert ({sig_fa_1_co, sig_fa_1_s} == sig_fa_1_a + sig_fa_1_b + sig_fa_1_ci)
      else $error("%m fa1 sum mismatch");
    assert ({sig_fa_2_co, sig_fa_2_s} == sig_fa_2_a + sig_fa_2_b + sig_fa_2_ci)
      else $error("%m fa2 sum mismatch");
    assert ({sig_fa_3_co, sig_fa_3_s} == sig_fa_3_a + sig_fa_3_b + sig_fa_3_ci)
      else $error("%m fa3 sum mismatch");

    // Sum-bit mapping
    assert (s[0] == sig_fa_0_s)   else $error("%m s[0]!=fa0.s");
    assert (s[1] == sig_fa_1_s)   else $error("%m s[1]!=fa1.s");
    assert (s[2] == sig_fa_2_s)   else $error("%m s[2]!=fa2.s");
    assert (s[3] == sig_fa_3_s)   else $error("%m s[3]!=fa3.s");

    // Concise but meaningful coverage
    if (ENABLE_COV) begin
      cover (co == 0);
      cover (co == 1);
      cover ({co,s} == 5'd0);   // 0+0+0
      cover ({co,s} == 5'd31);  // 15+15+1
      cover ((a ^ b) == 4'hF && ci == 1); // full carry propagate path exercised
    end
  end
endmodule

// Bind into DUTs
bind FullAdder   FullAdder_sva   fulladder_sva_i   (.a(a), .b(b), .ci(ci), .co(co), .s(s));
bind RippleAdder2 RippleAdder2_sva rippleadder2_sva_i
(
  .a(a), .b(b), .ci(ci), .co(co), .s(s),
  .c(c),
  .sig_fa_0_a(sig_fa_0_a), .sig_fa_0_b(sig_fa_0_b), .sig_fa_0_ci(sig_fa_0_ci), .sig_fa_0_co(sig_fa_0_co), .sig_fa_0_s(sig_fa_0_s),
  .sig_fa_1_a(sig_fa_1_a), .sig_fa_1_b(sig_fa_1_b), .sig_fa_1_ci(sig_fa_1_ci), .sig_fa_1_co(sig_fa_1_co), .sig_fa_1_s(sig_fa_1_s),
  .sig_fa_2_a(sig_fa_2_a), .sig_fa_2_b(sig_fa_2_b), .sig_fa_2_ci(sig_fa_2_ci), .sig_fa_2_co(sig_fa_2_co), .sig_fa_2_s(sig_fa_2_s),
  .sig_fa_3_a(sig_fa_3_a), .sig_fa_3_b(sig_fa_3_b), .sig_fa_3_ci(sig_fa_3_ci), .sig_fa_3_co(sig_fa_3_co), .sig_fa_3_s(sig_fa_3_s)
);