// SVA for LowPassFilter and SystolicFilter
// Focused, concise checks + useful coverage

// ---------- SystolicFilter assertions ----------
module SystolicFilter_sva (
  input logic                  clk,
  input logic                  filter_onoff,
  input logic signed [15:0]    audio_in,
  input logic        [15:0]    filter_out
);
  default clocking cb @(posedge clk); endclocking

  // Track past-valid and whether we ever enabled (to avoid false X failures)
  logic past_valid, seen_enable;
  always_ff @(posedge clk) begin
    past_valid  <= 1'b1;
    if (filter_onoff) seen_enable <= 1'b1;
  end

  // Control must be known
  a_ctrl_known: assert property ( !$isunknown(filter_onoff) );

  // Update behavior: when enabled, next-cycle filter_out equals prior audio_in
  a_update_on_en: assert property ( disable iff (!past_valid)
    filter_onoff |-> (filter_out == $past(audio_in))
  );

  // Hold behavior: when disabled, filter_out must not change
  a_hold_on_dis: assert property ( disable iff (!past_valid)
    !filter_onoff |-> $stable(filter_out)
  );

  // Once we have ever enabled, filter_out must be known thereafter
  a_known_after_first_update: assert property ( disable iff (!past_valid)
    seen_enable |-> !$isunknown(filter_out)
  );

  // Coverage
  c_enable_update:  cover property ( disable iff (!past_valid)
    filter_onoff ##1 (filter_out == $past(audio_in))
  );
  c_disable_hold:   cover property ( disable iff (!past_valid)
    !filter_onoff ##1 $stable(filter_out)
  );
  c_toggle_010:     cover property ( !filter_onoff ##1 filter_onoff ##1 !filter_onoff );
endmodule

bind SystolicFilter SystolicFilter_sva
  (.clk(clk),
   .filter_onoff(filter_onoff),
   .audio_in(audio_in),
   .filter_out(filter_out));

// ---------- LowPassFilter assertions ----------
module LowPassFilter_sva (
  input logic                  clk,
  input logic                  filter_onoff,
  input logic signed [15:0]    audio_in,
  input logic signed [15:0]    audio_out,
  // bind to internal wire
  input logic        [15:0]    filter_out
);
  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Control must be known
  a_ctrl_known: assert property ( !$isunknown(filter_onoff) );

  // Mux correctness (structural): output matches selected source
  a_mux_correct: assert property (
    audio_out == (filter_onoff ? $signed(filter_out) : audio_in)
  );

  // End-to-end functional check (enabled back-to-back):
  // with enable in two consecutive cycles, output reflects prior input
  a_e2e_when_enabled: assert property ( disable iff (!past_valid)
    (filter_onoff && $past(filter_onoff)) |-> (audio_out == $past(audio_in))
  );

  // Coverage
  c_passthrough: cover property ( !filter_onoff && (audio_out == audio_in) );
  c_filterpath:  cover property ( filter_onoff  && (audio_out == $signed(filter_out)) );
  c_toggle_010:  cover property ( !filter_onoff ##1 filter_onoff ##1 !filter_onoff );
endmodule

bind LowPassFilter LowPassFilter_sva
  (.clk(clk),
   .filter_onoff(filter_onoff),
   .audio_in(audio_in),
   .audio_out(audio_out),
   .filter_out(filter_out));