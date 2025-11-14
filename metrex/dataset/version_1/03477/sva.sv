// SVA for pipelined_adder and top_module (concise, high-quality checks + coverage)

module pipelined_adder_sva (
  input logic [7:0] a, b,
  input logic [7:0] s,
  input logic       overflow,
  input logic [7:0] p, g, c
);
  // event to sample concurrent cover on any comb change
  event comb_ev;
  always_comb -> comb_ev;

  // core combinational checks and golden model
  always_comb begin
    // no X/Z on I/Os and key internals
    assert (!$isunknown({a,b,s,overflow})) else $error("X/Z on I/O");
    assert (!$isunknown({p,g,c})) else $error("X/Z on p/g/c");

    // bit 0
    assert (p[0] === (a[0]^b[0])) else $error("p[0] mismatch");
    assert (g[0] === (a[0]&b[0])) else $error("g[0] mismatch");
    assert (c[0] === g[0])        else $error("c[0] mismatch");

    // bits 1..7 relationships + canonical carry equations
    for (int i=1; i<8; i++) begin
      logic cin;
      cin = c[i-1];
      assert (p[i] === (a[i]^b[i]^cin))                                   else $error("p[%0d]", i);
      assert (g[i] === ((a[i]&b[i]) | (a[i]&cin) | (b[i]&cin)))            else $error("g[%0d]", i);
      assert (c[i] === ((a[i]&b[i]) | (g[i]&cin)))                         else $error("c_rel[%0d]", i);
      assert (c[i] === g[i])                                               else $error("c==g[%0d]", i); // algebraic identity here
    end

    // golden ripple-adder model for s and overflow
    logic        carry;
    logic [7:0]  esum;
    carry = 1'b0;
    for (int j=0; j<8; j++) begin
      esum[j] = a[j]^b[j]^carry;
      carry   = (a[j]&b[j]) | ((a[j]^b[j]) & carry);
    end
    assert (s === esum)                                  else $error("s != a+b");
    assert (overflow === ((a[7]==b[7]) && (esum[7]!=a[7]))) else $error("overflow != signed overflow");
  end

  // compact coverage
  cover property (@(comb_ev) overflow);
  cover property (@(comb_ev) !overflow);
  cover property (@(comb_ev) (a==8'h00 && b==8'h00));                  // zero + zero
  cover property (@(comb_ev) (a==8'hFF && b==8'h01 && !overflow));     // carry-out, no signed ovf
  cover property (@(comb_ev) (a==8'h7F && b==8'h01 && overflow));      // +127 + 1 -> ovf
  cover property (@(comb_ev) (a==8'h80 && b==8'h80 && overflow));      // -128 + -128 -> ovf
  cover property (@(comb_ev) (c[6]^c[7]));                             // carry into/out of MSB differ
endmodule

bind pipelined_adder pipelined_adder_sva
  sva_adder(.a(a), .b(b), .s(s), .overflow(overflow), .p(p), .g(g), .c(c));


// Top-level checks to ensure module composition meets spec
module top_module_sva (
  input logic [7:0] a, b, s,
  input logic       overflow
);
  event comb_ev; always_comb -> comb_ev;

  always_comb begin
    assert (!$isunknown({a,b,s,overflow})) else $error("X/Z on top I/O");
    // top-level sum must be a+b (mod 256)
    assert (s === (a + b)) else $error("top: s != a+b");
    // overflow must correspond to the delivered s (signed overflow of s)
    assert (overflow === ((a[7]==b[7]) && (s[7]!=a[7])))
      else $error("top: overflow != signed overflow of s");
  end

  // compact top-level coverage
  cover property (@(comb_ev) (a==8'h7F && b==8'h01 && overflow));
  cover property (@(comb_ev) (a==8'h80 && b==8'h80 && overflow));
  cover property (@(comb_ev) (a==8'hFF && b==8'h01 && !overflow));
endmodule

bind top_module top_module_sva
  sva_top(.a(a), .b(b), .s(s), .overflow(overflow));