// SVA for carry_lookahead_adder and top_module
// Bind modules (no DUT changes required)

// Bind for carry_lookahead_adder
module carry_lookahead_adder_sva_bind;
  bind carry_lookahead_adder cla_sva();
endmodule

module cla_sva();
  // Combinational assertions and coverage
  always_comb begin
    // No X/Z on outputs; functional correctness
    if (!$isunknown({a,b,cin})) begin
      assert ({cout,sum} == ({1'b0,a} + {1'b0,b} + cin))
        else $error("CLA: {cout,sum} != a+b+cin");
      assert (!$isunknown({g,p,c})) else $error("CLA: X/Z on g/p/c with known inputs");
      assert (!$isunknown({sum,cout})) else $error("CLA: X/Z on outputs with known inputs");
    end

    // g/p correctness (LSBs only)
    assert (g[0] == (a[0] & b[0]));
    assert (g[1] == (a[1] & b[1]));
    assert (g[2] == (a[2] & b[2]));
    assert (g[3] == (a[3] & b[3]));
    assert (p[0] == (a[0] | b[0]));
    assert (p[1] == (a[1] | b[1]));
    assert (p[2] == (a[2] | b[2]));
    assert (p[3] == (a[3] | b[3]));

    // Carry lookahead equations
    assert (c[0] == cin);
    assert (c[1] == (g[0] | (p[0] & cin)));
    assert (c[2] == (g[1] | (p[1] & g[0]) | (p[1] & p[0] & cin)));
    assert (c[3] == (g[2] | (p[2] & g[1]) | (p[2] & p[1] & g[0]) | (p[2] & p[1] & p[0] & cin)));

    // Basic coverage
    cover (cin==0);
    cover (cin==1);
    cover (c == 4'b0000);
    cover (c == 4'b0001);
    cover (c == 4'b0011);
    cover (c == 4'b0111);
    cover (c == 4'b1111);
    cover (&g);
    cover (&p);
    cover (&p && !(&g) && cin); // ripple through via propagate
  end
endmodule

// Bind for top_module
module top_module_sva_bind;
  bind top_module top_sva();
endmodule

module top_sva();
  always_comb begin
    // 32-bit sum correctness (modulo 32)
    if (!$isunknown({a,b})) begin
      assert ({1'b0,sum} == ({1'b0,a} + {1'b0,b}))
        else $error("TOP: sum != a+b");
      assert (!$isunknown(sum)) else $error("TOP: X/Z on sum with known inputs");
    end

    // Carry handoff and per-half correctness
    assert (cin == adder_low.cout);
    assert (cin == adder_high.cin);
    assert ({cin, sum[15:0]} == ({1'b0, a[15:0]} + {1'b0, b[15:0]}));
    assert (sum[31:16] == (a[31:16] + b[31:16] + cin));

    // Coverage: carry between halves
    cover (cin==0);
    cover (cin==1);
  end
endmodule