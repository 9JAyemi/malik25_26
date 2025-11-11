// SVA for carry_lookahead_gen
// Bind-in assertion module (no DUT changes required)

module carry_lookahead_gen_sva;
  // This module is bound into carry_lookahead_gen and can see its internals.

  // Guard all checks from Xs on the used inputs
  function bit clean_inputs;
    clean_inputs = !$isunknown({g[2:0], p[2:0], cin});
  endfunction

  always_comb begin
    if (clean_inputs()) begin
      // Low-level gate intent
      assert (cout[0] == cin);
      assert (and_out_1 === (p[0] & cin));
      assert (or_out_1  === (g[0] | and_out_1));

      assert (and_out_2 === (p[1] & g[0]));
      assert (and_out_3 === (p[1] & p[0] & cin));
      assert (or_out_2  === (g[1] | and_out_3 | and_out_2));

      assert (and_out_4 === (p[2] & g[1]));
      assert (and_out_5 === (p[2] & p[1] & g[0]));
      assert (and_out_6 === (p[2] & p[1] & p[0] & cin));
      assert (or_out_3  === (g[2] | and_out_6 | and_out_5 | and_out_4));

      assert (cout[1] == or_out_1);
      assert (cout[2] == or_out_2);
      assert (cout[3] == or_out_3);

      // High-level equivalence (independent of g[3], p[3])
      logic c1, c2, c3;
      c1 = g[0] | (p[0] & cin);
      c2 = g[1] | (p[1] & g[0]) | (p[1] & p[0] & cin);
      c3 = g[2] | (p[2] & g[1]) | (p[2] & p[1] & g[0]) | (p[2] & p[1] & p[0] & cin);
      assert (cout == {c3, c2, c1, cin});

      // No X on outputs when inputs are clean
      assert (!$isunknown(cout));
    end
  end

  // Functional coverage: each carry term source hit at least once
  // C1 sources
  always_comb if (clean_inputs()) begin
    cover (or_out_1 && g[0]);
    cover (or_out_1 && !g[0] && p[0] && cin);
    // C2 sources
    cover (or_out_2 && g[1]);
    cover (or_out_2 && !g[1] && p[1] && g[0]);
    cover (or_out_2 && !g[1] && !(p[1] && g[0]) && p[1] && p[0] && cin);
    // C3 sources
    cover (or_out_3 && g[2]);
    cover (or_out_3 && !g[2] && p[2] && g[1]);
    cover (or_out_3 && !g[2] && !(p[2] && g[1]) && p[2] && p[1] && g[0]);
    cover (or_out_3 && !g[2] && !(p[2] && g[1]) && !(p[2] && p[1] && g[0])
           && p[2] && p[1] && p[0] && cin);
  end

endmodule

bind carry_lookahead_gen carry_lookahead_gen_sva cla_sva();