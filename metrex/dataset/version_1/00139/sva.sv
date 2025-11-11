// SVA for mux2to1: concise, high-quality checks and coverage.
// Bind into the DUT to keep design untouched.

module mux2to1_sva(input logic a, b, s, out);

  // 1) Sanity: no X/Z on any port when sampled
  a_no_x:    assert property (@(a or b or s or out) !$isunknown({a,b,s,out}));

  // 2) Functional correctness: out equals selected input on any input/select change
  p_func:    assert property (@(a or b or s) out == (s ? b : a));

  // 3) Out only changes when some input/select changes (no spurious glitches)
  p_no_spur: assert property (disable iff ($isunknown({a,b,s,out}))
                              @(posedge out or negedge out) $changed({a,b,s}));

  // Coverage
  // - Both selections exercised
  c_sel0:    cover property (@(a or b or s) (s==1'b0) && (out==a));
  c_sel1:    cover property (@(a or b or s) (s==1'b1) && (out==b));

  // - Select toggles while inputs differ (demonstrates true muxing)
  c_s_rise:  cover property (@(posedge s) (a!=b) && (out==b));
  c_s_fall:  cover property (@(negedge s) (a!=b) && (out==a));

  // - Data path toggles propagate through when selected
  c_a_path:  cover property (@(posedge a or negedge a) (s==1'b0) && $changed(out));
  c_b_path:  cover property (@(posedge b or negedge b) (s==1'b1) && $changed(out));

endmodule

bind mux2to1 mux2to1_sva u_mux2to1_sva(.a(a), .b(b), .s(s), .out(out));