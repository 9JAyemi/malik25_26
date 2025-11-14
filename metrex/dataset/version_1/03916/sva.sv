// SVA for mux4to1
module mux4to1_sva (
  input logic [3:0] in,
  input logic [1:0] sel,
  input logic       out
);
  // Helpers
  let clean = !$isunknown({in, sel, out});
  let ref   = in[sel];

  // No X/Z on any important signal
  ap_clean: assert property (@(in or sel or out) clean)
    else $error("mux4to1: X/Z detected on in/sel/out");

  // Functional equivalence after delta (zero-cycle settle)
  ap_func: assert property (disable iff (!clean)
                            @(in or sel or out) 1'b1 |-> ##0 (out == ref))
    else $error("mux4to1: out != in[sel]");

  // Non-selected inputs must not affect out when sel is stable
  ap_nonselected_no_effect: assert property (disable iff (!clean)
                            @(in or sel) $stable(sel) && !$changed(in[sel]) |-> ##0 $stable(out))
    else $error("mux4to1: out changed without sel or selected input change");

  // Selected input change must propagate to out (with zero-cycle settle)
  ap_selected_drives_out: assert property (disable iff (!clean)
                            @(in or sel) $stable(sel) && $changed(in[sel]) |-> ##0 $changed(out))
    else $error("mux4to1: selected input change did not propagate to out");

  // Coverage: see each select value with both data polarities
  c_sel0_0: cover property (@(in or sel) sel==2'b00 && in[0]==1'b0);
  c_sel0_1: cover property (@(in or sel) sel==2'b00 && in[0]==1'b1);
  c_sel1_0: cover property (@(in or sel) sel==2'b01 && in[1]==1'b0);
  c_sel1_1: cover property (@(in or sel) sel==2'b01 && in[1]==1'b1);
  c_sel2_0: cover property (@(in or sel) sel==2'b10 && in[2]==1'b0);
  c_sel2_1: cover property (@(in or sel) sel==2'b10 && in[2]==1'b1);
  c_sel3_0: cover property (@(in or sel) sel==2'b11 && in[3]==1'b0);
  c_sel3_1: cover property (@(in or sel) sel==2'b11 && in[3]==1'b1);

  // Coverage: output toggles; select bits toggle
  c_out_rise: cover property (@(out) $rose(out));
  c_out_fall: cover property (@(out) $fell(out));
  c_sel0_tgl: cover property (@(sel) $changed(sel[0]));
  c_sel1_tgl: cover property (@(sel) $changed(sel[1]));
endmodule

// Bind into DUT
bind mux4to1 mux4to1_sva sva(.in(in), .sel(sel), .out(out));