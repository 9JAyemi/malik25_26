// SVA checker for mux4to1
module mux4to1_sva (
  input logic [3:0] in,
  input logic [1:0] sel,
  input logic       out
);

  // Functional equivalence (handles X/Z on sel -> default 0)
  assert property (@(in or sel or out)
    1'b1 |-> ##0 ( $isunknown(sel) ? (out === 1'b0) : (out === in[sel]) )
  ) else $error("mux4to1 func mismatch: sel=%b in=%b out=%b", sel, in, out);

  // With stable sel, output changes only if selected input changes
  assert property (@(in or sel or out)
    !$isunknown(sel) && $stable(sel) && $changed(out) |-> $changed(in[sel])
  ) else $error("mux4to1 spurious out change: sel=%b in=%b out=%b", sel, in, out);

  // With stable sel, selected input changes reflect immediately at out
  assert property (@(in or sel or out)
    !$isunknown(sel) && $stable(sel) && $changed(in[sel])
      |-> ##0 ($changed(out) && out === in[sel])
  ) else $error("mux4to1 transparency fail: sel=%b in=%b out=%b", sel, in, out);

  // Coverage: each select mapping observed
  genvar i;
  generate
    for (i = 0; i < 4; i++) begin : C
      cover property (@(in or sel or out) sel == i ##0 (out === in[i]));
      cover property (@(in or sel or out) sel == i && $rose(in[i]) ##0 $rose(out));
      cover property (@(in or sel or out) sel == i && $fell(in[i]) ##0 $fell(out));
    end
  endgenerate
  // Coverage: default case on X/Z select drives 0
  cover property (@(in or sel or out) $isunknown(sel) ##0 (out === 1'b0));

endmodule

// Bind into the DUT
bind mux4to1 mux4to1_sva u_mux4to1_sva (.in(in), .sel(sel), .out(out));