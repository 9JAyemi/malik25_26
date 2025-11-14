// SVA for clock_gate / TLATNTSCAX2TS
module clock_gate_sva (input clk, input en, input te, input enclk);
  // guard $past
  logic past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid || $isunknown({clk,en,te,enclk}));

  // Core functional spec: next enclk = (en ? te : hold)
  ap_func: assert property ( enclk == ($past(en) ? $past(te) : $past(enclk)) );

  // If enabled, sample te; if disabled, hold (redundant but explicit)
  ap_en_update: assert property ($past(en) |-> enclk == $past(te));
  ap_hold     : assert property (!$past(en) |-> enclk == $past(enclk));

  // No mid-cycle updates (sampled at negedge as a glitch sentinel)
  ap_no_change_negedge: assert property (@(negedge clk) $stable(enclk));

  // Any change across cycles must be due to enable
  ap_change_implies_en: assert property ($changed(enclk) |-> $past(en));

  // Coverage
  cp_rise: cover property ($past(en) && $past(te)  && $rose(enclk));
  cp_fall: cover property ($past(en) && !$past(te) && $fell(enclk));
  cp_hold: cover property (!$past(en) && enclk == $past(enclk));
endmodule

// Bind to both top and the cell instance
bind clock_gate      clock_gate_sva u_clock_gate_sva (.clk(clk), .en(en), .te(te), .enclk(enclk));
bind TLATNTSCAX2TS   clock_gate_sva u_tlat_sva       (.clk(CK),  .en(E),  .te(SE), .enclk(ECK));