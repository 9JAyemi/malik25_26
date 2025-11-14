// SVA for dff_en: concise, high-quality checks and coverage
module dff_en_sva #(parameter width_p = 1) ();
  // Accesses DUT signals via bind into dff_en scope
  logic past_v;
  initial past_v = 1'b0;
  always @(posedge clock_i) past_v <= 1'b1;

  default clocking cb @(posedge clock_i); endclocking
  default disable iff (!past_v);

  // Combinational mirror: data_o must always equal internal state
  assert property (@(posedge clock_i or data_r or data_o) data_o == data_r);

  // No X/Z on state/outputs after first edge
  assert property (!$isunknown({data_r, data_o}));

  // Capture on enable: next state equals sampled input
  assert property (en_i |=> data_r == $past(data_i));
  assert property (en_i |=> data_o == $past(data_i));

  // Hold when disabled
  assert property (!en_i |=> data_r == $past(data_r));
  assert property (!en_i |=> data_o == $past(data_o));

  // Any state/output change implies enable was 1 on the launching edge
  assert property ($changed(data_r) |-> $past(en_i));
  assert property ($changed(data_o) |-> $past(en_i));

  // Input must be known when used
  assert property (en_i |-> !$isunknown(data_i));

  // Coverage
  cover property (en_i ##1 $changed(data_o) && data_o == $past(data_i));         // capture event
  cover property (!en_i [*2] ##1 !$changed(data_o));                              // hold path
  cover property (en_i ##1 $changed(data_o) ##1 en_i ##1 $changed(data_o));       // back-to-back captures
endmodule

// Bind into the DUT
bind dff_en dff_en_sva #(.width_p(width_p)) dff_en_sva_i();