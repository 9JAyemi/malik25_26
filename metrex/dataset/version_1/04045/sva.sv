// SVA for p_aoi222 (AOI222: q == ~((a&b)|(c&d)|(e&f)))
module p_aoi222_sva (
  input logic a, b, c, d, e, f,
  input logic q,
  input logic [1:0] internal_0n,
  input logic [2:0] int_0n
);

  // Immediate assertions: functional and structural, 4-state aware
  always_comb begin
    logic p0 = a & b;
    logic p1 = c & d;
    logic p2 = e & f;

    assert (q === ~((p0) | (p1) | (p2)))
      else $error("AOI222 functional mismatch: q vs ~(a&b | c&d | e&f)");

    assert (int_0n[0] === p0) else $error("int_0n[0] != a&b");
    assert (int_0n[1] === p1) else $error("int_0n[1] != c&d");
    assert (int_0n[2] === p2) else $error("int_0n[2] != e&f");
    assert (internal_0n[0] === ~(int_0n[0] | int_0n[1]))
      else $error("internal_0n[0] != ~(int_0n[0]|int_0n[1])");
    assert (internal_0n[1] === ~int_0n[2])
      else $error("internal_0n[1] != ~int_0n[2]");
    assert (q === (internal_0n[0] & internal_0n[1]))
      else $error("q != internal_0n[0] & internal_0n[1]");

    // No X/Z on internals/output when inputs are known
    if (!$isunknown({a,b,c,d,e,f})) begin
      assert (!$isunknown({int_0n, internal_0n, q}))
        else $error("Unknown/Z on internal/output with known inputs");
    end
  end

  // Concurrent functional check sampled on any input change
  property p_func;
    @(a or b or c or d or e or f)
      1 |-> (q == ~((a & b) | (c & d) | (e & f)));
  endproperty
  assert property (p_func);

  // Coverage: key functional scenarios
  cover property (@(a or b or c or d or e or f) !(a&b) && !(c&d) && !(e&f) && q);          // none asserted
  cover property (@(a or b or c or d or e or f) (a&b) && !(c&d) && !(e&f) && !q);          // only a&b
  cover property (@(a or b or c or d or e or f) !(a&b) && (c&d) && !(e&f) && !q);          // only c&d
  cover property (@(a or b or c or d or e or f) !(a&b) && !(c&d) && (e&f) && !q);          // only e&f
  cover property (@(a or b or c or d or e or f) (a&b) && (c&d) && !(e&f) && !q);           // two terms: ab,cd
  cover property (@(a or b or c or d or e or f) (a&b) && !(c&d) && (e&f) && !q);           // two terms: ab,ef
  cover property (@(a or b or c or d or e or f) !(a&b) && (c&d) && (e&f) && !q);           // two terms: cd,ef
  cover property (@(a or b or c or d or e or f) (a&b) && (c&d) && (e&f) && !q);            // all three
  cover property (@(a or b or c or d or e or f) $rose(q));
  cover property (@(a or b or c or d or e or f) $fell(q));

endmodule

// Bind into DUT to observe internals
bind p_aoi222 p_aoi222_sva sva (
  .a(a), .b(b), .c(c), .d(d), .e(e), .f(f),
  .q(q),
  .internal_0n(internal_0n),
  .int_0n(int_0n)
);