// SVA for tone_detection_generation
// Bind example:
// bind tone_detection_generation tone_detection_generation_sva sva (.*,
//   .phase_acc(phase_acc), .phase_inc(phase_inc), .tone(tone),
//   .threshold(threshold), .sample_count(sample_count),
//   .sample_rate(sample_rate), .sample_period(sample_period),
//   .sample_threshold(sample_threshold), .det_flag(det_flag),
//   .gen_flag(gen_flag), .gen_en(gen_en), .in_sample(in_sample),
//   .gen_sample(gen_sample));

module tone_detection_generation_sva (
  input  logic                 clk,
  input  logic                 reset,
  input  logic                 in,
  input  logic                 freq,
  input  logic                 det,
  input  logic                 gen,

  input  logic [31:0]          phase_acc,
  input  logic [31:0]          phase_inc,
  input  logic [31:0]          tone,
  input  logic [31:0]          threshold,
  input  logic [31:0]          sample_count,
  input  logic [31:0]          sample_rate,
  input  logic [31:0]          sample_period,
  input  logic [31:0]          sample_threshold,
  input  logic                 det_flag,
  input  logic                 gen_flag,
  input  logic                 gen_en,
  input  logic [31:0]          in_sample,
  input  logic [31:0]          gen_sample
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Global sanity (no X/Z on key outputs/controls)
  assert property (!$isunknown({det, gen, gen_en, gen_flag, det_flag, tone[0], phase_acc[31]}));

  // Synchronous reset values (sample_rate is constant, not reset)
  assert property (@(posedge clk)
    reset |=> phase_acc==0 && phase_inc==0 && tone==0 && threshold==0 &&
             sample_count==0 && sample_period==0 && sample_threshold==0 &&
             det_flag==0 && gen_flag==0 && gen_en==0 && det==0 && gen==0);

  // Sample rate must remain constant at 48000
  assert property (sample_rate == 32'd48000);

  // Input sampling
  assert property (in_sample == $past(in));

  // Generator enable follows freq>0 (1-cycle latency due to non-blocking)
  assert property (gen_en == $past(freq > 0));

  // Phase increment computation when freq>0 (as coded)
  assert property ( $past(freq > 0) |-> phase_inc == (($past(freq) << 32) / 32'd48000) );

  // Phase accumulator and tone update obey final gen_en-controlled block
  assert property ( $past(gen_en) |-> phase_acc == $past(phase_acc) + $past(phase_inc) );
  assert property ( !$past(gen_en) |-> phase_acc == 32'd0 );

  assert property ( $past(gen_en) |-> tone == ($past(phase_acc[31]) ? 32'hFFFF_FFFF : 32'h0000_0000) );
  assert property ( !$past(gen_en) |-> tone == 32'h0000_0000 );

  // gen_flag mirrors prior gen_en; gen output mirrors prior gen_sample when enabled
  assert property (gen_flag == $past(gen_en));
  assert property (gen == ($past(gen_en) ? $past(gen_sample) : 1'b0));

  // gen_sample update: gated by current-cycle gen_flag && gen_en (both sampled in past)
  assert property ( gen_sample == ($past(gen_flag && gen_en) ? $past(tone) : 32'd0) );

  // Detector: sample_count reset when in_sample <= threshold
  assert property ( $past(in_sample) <= $past(threshold) |-> sample_count == 32'd0 );

  // Detector: arming event (det_flag rises) captures period and threshold, clears count
  assert property ( !$past(det_flag) && ($past(sample_count) >= $past(sample_threshold))
                    |-> det_flag && sample_period == $past(sample_count) &&
                        sample_count == 32'd0 && threshold == $past(in_sample) && !det );

  // Detector: while armed but not reached period -> det must be 0
  assert property ( $past(det_flag) && !($past(sample_count) >= $past(sample_period)) |-> !det );

  // Detector: when period reached while armed -> single-cycle det pulse and disarm
  assert property ( $past(det_flag) && ($past(sample_count) >= $past(sample_period))
                    |-> det && !det_flag );
  assert property ( det |=> !det ); // det pulse is one cycle

  // Outputs zero when not enabled
  assert property ( !$past(gen_en) |-> gen == 1'b0 );

  // Coverage
  cover property ( $rose(det_flag) );
  cover property ( det );
  cover property ( $rose(gen_en) );
  cover property ( gen_en && gen );
  cover property ( gen_en && tone==32'hFFFF_FFFF );
  cover property ( gen_en && $changed(phase_acc[31]) ); // observe tone MSB toggle opportunity

endmodule