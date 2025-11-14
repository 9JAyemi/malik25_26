// SVA for lookahead. Bind this to the DUT.
// Focused, combinational, high-quality checks plus key functional coverage.

module lookahead_sva(
  input  logic [3:0] p, g,
  input  logic       c_in,
  input  logic [2:0] c,
  input  logic       c_out,
  input  logic       P, G
);

  default clocking cb @(*); endclocking

  // Golden expressions
  logic exp_c0, exp_c1, exp_c2, exp_P, exp_G, exp_cout;
  assign exp_c0   = g[0] | (p[0] & c_in);
  assign exp_c1   = g[1] | (g[0] & p[1]) | (p[1] & p[0] & c_in);
  assign exp_c2   = g[2] | (g[1] & p[2]) | (g[0] & p[1] & p[2]) | (p[2] & p[1] & p[0] & c_in);
  assign exp_P    = &p;
  assign exp_G    = g[3] | (g[2] & p[3]) | (g[1] & p[2] & p[3]) | (p[3] & p[2] & p[1] & g[0]);
  assign exp_cout = exp_G | (exp_P & c_in);

  // Equivalence assertions (primary spec)
  ap_c0:    assert property (c[0]   == exp_c0);
  ap_c1:    assert property (c[1]   == exp_c1);
  ap_c2:    assert property (c[2]   == exp_c2);
  ap_P:     assert property (P      == exp_P);
  ap_G:     assert property (G      == exp_G);
  ap_cout:  assert property (c_out  == exp_cout);

  // Cross-consistency: Cout must match G | (P & Cin) using DUT P/G
  ap_cout_consistency: assert property (c_out == (G | (P & c_in)));

  // No-X propagation: known inputs => known outputs
  ap_no_x:  assert property (!$isunknown({p,g,c_in}) |-> !$isunknown({c,c_out,P,G}));

  // Sanity implications (useful for debug, concise)
  ap_c0_g0_forces1:   assert property (g[0] |-> c[0]);
  ap_c0_no_prop_no_gen_zero: assert property ((!p[0] && !g[0]) |-> !c[0]);
  ap_c0_prop_only_tracks_cin: assert property (( p[0] && !g[0]) |-> (c[0] == c_in));

  // Functional coverage: exercise each carry path and group terms
  // Group propagate/generate scenarios
  cp_P_all:           cover property (exp_P && !exp_G);
  cp_G_any:           cover property (exp_G);
  cp_G_g3:            cover property (g[3] && G);
  cp_G_p3g2:          cover property (p[3] && g[2] && G);
  cp_G_p3p2g1:        cover property (p[3] && p[2] && g[1] && G);
  cp_G_p3p2p1g0:      cover property (p[3] && p[2] && p[1] && g[0] && G);

  // c[2] carry path scenarios
  cp_c2_g2:           cover property (g[2] && c[2]);
  cp_c2_g1p2:         cover property (g[1] && p[2] && c[2]);
  cp_c2_g0p1p2:       cover property (g[0] && p[1] && p[2] && c[2]);
  cp_c2_prop_chain:   cover property (p[2] && p[1] && p[0] && c_in && c[2]);

  // End-to-end propagate chain cases
  cp_all_zero:        cover property (!|{p,g,c_in} && !P && !G && !c_out && (c==3'b000));
  cp_full_prop_cin1:  cover property (&p && !|g &&  c_in &&  c_out);
  cp_full_prop_cin0:  cover property (&p && !|g && !c_in && !c_out);

endmodule

// Bind to DUT
bind lookahead lookahead_sva sva_inst(.*);