// SVA for mux_4to1 — concise, quality-focused checks and coverage
module mux_4to1_sva (
  input logic [3:0] in,
  input logic [1:0] sel,
  input logic       out
);

  // Clockless concurrent SVA using an event driven by relevant comb signals
  event comb_ev;
  always @(in or sel or out) -> comb_ev;
  clocking cb @(comb_ev); endclocking
  default clocking cb;

  // 1) Inputs sanity
  property p_sel_known; !$isunknown(sel); endproperty
  assert property (p_sel_known) else $error("mux_4to1: sel has X/Z");

  // 2) Functional correctness (4-state compare); only when sel known
  property p_func; !$isunknown(sel) |-> (out === in[sel]); endproperty
  assert property (p_func) else $error("mux_4to1: out != in[sel]");

  // 3) No X/Z on out when sel and selected input are known
  property p_no_x_out; (!$isunknown(sel) && !$isunknown(in[sel])) |-> !$isunknown(out); endproperty
  assert property (p_no_x_out) else $error("mux_4to1: out X/Z while sel and selected input known");

  // 4) Zero-latency propagation on cause (sel or selected input change)
  property p_zero_latency;
    (!$isunknown(sel) && ($changed(sel) || $changed(in[sel]))) |-> ##0 (out === in[sel]);
  endproperty
  assert property (p_zero_latency) else $error("mux_4to1: zero-latency propagation failure");

  // 5) No spurious out changes without cause
  property p_no_spurious_out_change;
    (!$isunknown(sel) && !$changed(sel) && !$changed(in[sel])) |-> !$changed(out);
  endproperty
  assert property (p_no_spurious_out_change) else $error("mux_4to1: out changed without cause");

  // Functional coverage
  cover property (sel == 2'b00);
  cover property (sel == 2'b01);
  cover property (sel == 2'b10);
  cover property (sel == 2'b11);

  cover property ((sel==2'b00 && $changed(in[0])) ##0 $changed(out));
  cover property ((sel==2'b01 && $changed(in[1])) ##0 $changed(out));
  cover property ((sel==2'b10 && $changed(in[2])) ##0 $changed(out));
  cover property ((sel==2'b11 && $changed(in[3])) ##0 $changed(out));

  cover property (!$isunknown(sel) && $changed(sel) ##0 (out === in[sel]));

endmodule

bind mux_4to1 mux_4to1_sva u_mux_4to1_sva(.in(in), .sel(sel), .out(out));