// SVA for freq_synth: concise, high-quality checks and coverage
// Bind-friendly module – connects to DUT internals via bind port map.

module freq_synth_sva #(
  parameter int unsigned resolution      = 8,
  parameter int unsigned frequency_range = 100000000
)(
  input  logic         clk,
  input  logic [31:0]  ref_clk,
  input  logic [31:0]  out_freq,
  input  logic [31:0]  integer_value,
  input  logic [31:0]  synthesized_freq,
  input  logic [7:0]   synth_freq
);

  // Derived constants (64b for math safety)
  localparam int unsigned RES = resolution;
  localparam longint unsigned TWO_TO_RES = (1 << RES);
  localparam longint unsigned SCALE      = (frequency_range / TWO_TO_RES);

  // Static parameter sanity
  initial begin
    assert (RES > 0 && RES <= 31) else $error("resolution out of range");
    assert (frequency_range > 0) else $error("frequency_range must be > 0");
    assert (SCALE > 0) else $error("SCALE must be > 0");
  end

  // Clocking/disable for $past safety
  default clocking cb @(posedge clk); endclocking
  logic past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Helpers
  let U64(x) = longint unsigned'(x);

  // No divide-by-zero hazards (must hold every cycle after first)
  a_no_div0_ref_out: assert property ( $past(out_freq) != 32'd0 )
    else $error("Divide by zero: out_freq");
  a_no_div0_int_plus1: assert property ( $past(integer_value) != 32'hFFFF_FFFF )
    else $error("Divide by zero: integer_value+1");

  // Pipeline update correctness (NBA semantics)
  a_integer_update: assert property (
    $past(out_freq) != 0 |-> integer_value == ( $past(ref_clk) / $past(out_freq) ) - 1
  );

  a_synthesized_update: assert property (
    $past(integer_value) != 32'hFFFF_FFFF
      |-> synthesized_freq == $past(ref_clk) / ($past(integer_value) + 1)
  );

  a_synth_freq_update: assert property (
    synth_freq == $past(synthesized_freq) / SCALE
  );

  // Integer division floor properties (range-tight inequalities)
  a_floor_iv: assert property ( $past(out_freq) != 0 |->
    ( U64($past(out_freq)) * U64(integer_value + 1) ) <= U64($past(ref_clk)) &&
    U64($past(ref_clk)) < ( U64($past(out_freq)) * U64(integer_value + 2) )
  );

  let DEN = $past(integer_value) + 1;
  a_floor_syn: assert property ( $past(integer_value) != 32'hFFFF_FFFF |->
    ( U64(DEN) * U64(synthesized_freq) ) <= U64($past(ref_clk)) &&
    U64($past(ref_clk)) < ( U64(DEN) * (U64(synthesized_freq) + 1) )
  );

  // Output range (avoid truncation overflow beyond resolution)
  a_synth_freq_range: assert property (
    ( $past(synthesized_freq) / SCALE ) <= (TWO_TO_RES - 1)
  );

  // Stability: stable inputs => stable state (under safe denominators)
  a_stable_when_inputs_stable: assert property (
    $stable(ref_clk) && $stable(out_freq) &&
    $past(out_freq)!=0 && $past(integer_value)!=32'hFFFF_FFFF |->
      $stable(integer_value) && $stable(synthesized_freq) && $stable(synth_freq)
  );

  // Monotonicity of integer_value w.r.t out_freq when ref_clk stable
  a_monotonic_up: assert property (
    $stable(ref_clk) && $past(out_freq)!=0 && (out_freq > $past(out_freq))
      |-> integer_value <= $past(integer_value)
  );

  a_monotonic_down: assert property (
    $stable(ref_clk) && $past(out_freq)!=0 && (out_freq < $past(out_freq))
      |-> integer_value >= $past(integer_value)
  );

  // No X/Z on key state
  a_no_unknowns: assert property ( !$isunknown({integer_value, synthesized_freq, synth_freq}) );

  // Coverage
  c_iv_zero:        cover property ( integer_value == 32'd0 );
  c_iv_max:         cover property ( integer_value == 32'hFFFF_FFFF );
  c_sf_zero:        cover property ( synth_freq == 0 );
  c_sf_max:         cover property ( synth_freq == (TWO_TO_RES - 1) );
  c_outfreq_rise:   cover property ( $stable(ref_clk) && out_freq > $past(out_freq) ##1 integer_value < $past(integer_value) );
  c_outfreq_fall:   cover property ( $stable(ref_clk) && out_freq < $past(out_freq) ##1 integer_value > $past(integer_value) );

endmodule

// Example bind (place in a separate file or TB)
// bind freq_synth freq_synth_sva #(.resolution(resolution), .frequency_range(frequency_range))
//   freq_synth_sva_i (.*);