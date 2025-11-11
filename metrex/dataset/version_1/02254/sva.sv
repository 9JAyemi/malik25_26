// SVA/checkers for pipelined_add_sub and submodules.
// Bind-only; no DUT changes. Focused, end-to-end plus key local relations.
`ifndef PIPELINED_ADD_SUB_SVA
`define PIPELINED_ADD_SUB_SVA

// Top-level checker
module pipelined_add_sub_sva(
  input logic [31:0] a,
  input logic [31:0] b,
  input logic        sub,
  input logic [31:0] csa_out,
  input logic [31:0] cla_out,
  input logic [31:0] sum
);
  logic [31:0] exp;
  always_comb begin
    // X-prop sanity
    if (!$isunknown({a,b,sub})) begin
      assert (!$isunknown({csa_out,cla_out,sum})) else
        $error("pipelined_add_sub: X/Z on internal/output with known inputs");
    end
    // End-to-end: add/sub (wrap-around)
    exp = a + (sub ? (~b + 32'd1) : b);
    assert (sum == exp) else
      $error("pipelined_add_sub: sum mismatch exp=%0h got=%0h a=%0h b=%0h sub=%0b",
             exp, sum, a, b, sub);
    // Structural drive
    assert (sum == cla_out) else
      $error("pipelined_add_sub: sum not equal cla_out");
    // Basic coverage
    cover (sub==0 && a==32'h0 && b==32'h0);
    cover (sub==0 && a==32'hFFFF_FFFF && b==32'h1);     // carry out
    cover (sub==1 && a==32'h0 && b==32'h1);             // borrow
    cover (sub==1 && a==b);                             // result zero
    cover (sub==0 && a==32'hAAAA_AAAA && b==32'h5555_5555);
    cover (sub==1 && a==32'h8000_0000 && b==32'h1);
  end
endmodule
bind pipelined_add_sub pipelined_add_sub_sva u_pipelined_add_sub_sva(
  .a(a), .b(b), .sub(sub), .csa_out(csa_out), .cla_out(cla_out), .sum(sum)
);

// CSA checker
module csa_sva(
  input logic [31:0] a,
  input logic [31:0] b,
  input logic        c,
  input logic [31:0] s
);
  logic [31:0] exp_s;
  always_comb begin
    // Intended CSA equation (ensure scalar c replicates)
    exp_s = (a ^ b) ^ {32{c}} ^ (a & b);
    assert (s == exp_s) else
      $error("CSA: s mismatch exp=%0h got=%0h a=%0h b=%0h c=%0b", exp_s, s, a, b, c);
    if (!$isunknown({a,b,c})) assert(!$isunknown(s)) else
      $error("CSA: X/Z on s with known inputs");
    // Coverage
    cover (c==0);
    cover (c==1);
    cover (a==b);      // all generate
    cover (a==~b);     // all propagate
  end
endmodule
bind csa csa_sva u_csa_sva(.a(a), .b(b), .c(c), .s(s));

// gen_propagate checker
module gen_propagate_sva(
  input logic [31:0] a,
  input logic [31:0] b,
  input logic [31:0] p,
  input logic [31:0] g
);
  always_comb begin
    assert (p == (a ^ b)) else $error("gen_propagate: p != a^b");
    assert (g == (a & b)) else $error("gen_propagate: g != a&b");
    if (!$isunknown({a,b})) assert(!$isunknown({p,g})) else
      $error("gen_propagate: X/Z on p/g with known inputs");
    // Coverage
    cover (p==32'h0000_0000);
    cover (p==32'hFFFF_FFFF);
    cover (g==32'h0000_0000);
    cover (g==32'hFFFF_FFFF);
  end
endmodule
bind gen_propagate gen_propagate_sva u_gen_propagate_sva(.a(a), .b(b), .p(p), .g(g));

// CLA checker
module cla_sva(
  input logic [31:0] a,
  input logic [31:0] b,
  input logic [31:0] c,
  input logic [31:0] s
);
  logic [31:0] exp_s;
  always_comb begin
    // Spec-level: full 32b addition with c[0] as carry-in
    exp_s = a + b + c[0];
    assert (s == exp_s) else
      $error("CLA: s mismatch exp=%0h got=%0h a=%0h b=%0h c0=%0b", exp_s, s, a, b, c[0]);
    // Local p/g relations via ports are checked in gen_propagate_sva
    if (!$isunknown({a,b,c})) assert(!$isunknown(s)) else
      $error("CLA: X/Z on s with known inputs");
    // Coverage
    cover (c[0]==0);
    cover (c[0]==1);
    cover (a==32'hFFFF_FFFF && b==32'h0000_0001 && c[0]==0);
    cover (a==32'h0000_0000 && b==32'h0000_0000 && c[0]==1);
  end
endmodule
bind cla cla_sva u_cla_sva(.a(a), .b(b), .c(c), .s(s));

`endif