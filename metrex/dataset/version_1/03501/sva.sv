// SVA for tone_generator
// Bind into the DUT to check key behaviors concisely

bind tone_generator tone_generator_sva();

module tone_generator_sva;

  // Accesses bound instance scope (clk, rst, tone, audio_out, internal regs/params)
  default clocking cb @ (posedge clk); endclocking

  // 1) Reset and idle behavior
  assert property (rst |=> tone_counter==0 && tone_duration==0 && sample_counter==0 && sample_period==0 && tone_type==2'b00);
  assert property (disable iff (rst)
                   (tone==2'b00) |=> (tone_counter==0 && tone_duration==0 && sample_counter==0 && sample_period==0 && tone_type==2'b00));

  // 2) New tone programming
  assert property (disable iff (rst)
                   (tone!=2'b00 && tone!=tone_type)
                   |=> (tone_counter==0
                        && tone_duration==(t_duration*f_clk)
                        && sample_counter==0
                        && sample_period==(f_clk/f_tone)
                        && tone_type==$past(tone)));

  // 3) Active invariants while a tone is selected
  assert property (disable iff (rst)
                   (tone_type!=2'b00) |-> (sample_period==(f_clk/f_tone) && tone_duration==(t_duration*f_clk)));

  // 4) Run-state counter progression and sample wrap
  assert property (disable iff (rst)
                   (tone!=2'b00 && tone==tone_type && tone_counter < tone_duration)
                   |=> (tone_counter==$past(tone_counter)+1));

  assert property (disable iff (rst)
                   (tone!=2'b00 && tone==tone_type && tone_counter < tone_duration && sample_counter < sample_period)
                   |=> (sample_counter==$past(sample_counter)+1));

  assert property (disable iff (rst)
                   (tone!=2'b00 && tone==tone_type && tone_counter < tone_duration && sample_counter >= sample_period)
                   |=> (sample_counter==0));

  // 5) End-of-tone cleanup
  assert property (disable iff (rst)
                   (tone!=2'b00 && tone==tone_type && tone_counter >= tone_duration)
                   |=> (tone_counter==0 && tone_duration==0 && sample_counter==0 && sample_period==0 && tone_type==2'b00));

  // 6) Audio output correctness (matches spec expression)
  assert property (audio_out == (tone_counter >= (f_clk/(2*f_tone))));

  // 7) Simple X checks on key signals
  assert property (!$isunknown({tone, audio_out, tone_type}));

  // Coverage: new-tone select, sample wrap, tone completion, audio_out rising
  cover property (disable iff (rst) (tone!=2'b00 && tone!=tone_type));
  cover property (disable iff (rst) (tone!=2'b00 && tone==tone_type && sample_counter==sample_period) ##1 (sample_counter==0));
  cover property (disable iff (rst) (tone!=2'b00 && tone==tone_type && tone_counter==tone_duration) ##1 (tone_type==2'b00));
  cover property (disable iff (rst) $rose(audio_out));

endmodule