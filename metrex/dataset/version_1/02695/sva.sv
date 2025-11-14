// SVA checker for freq_synthesizer
// Bind with: bind freq_synthesizer freq_synthesizer_sva();

module freq_synthesizer_sva;

  // Bring DUT params into scope
  localparam int N     = n;
  localparam int M     = m;
  localparam int RATIO = f_out / f_ref;

  default clocking cb @(posedge ref_clk); endclocking

  // Start after first clock to avoid X at time 0 (no reset in DUT)
  logic started; initial started = 1'b0;
  always @(posedge ref_clk) started <= 1'b1;

  // X/Z sanity (after start)
  assert property (disable iff (!started)
                   !$isunknown({ctrl, counter, divider, phase, phase_accumulator,
                                phase_increment, phase_accumulator_next, syn_clk,
                                ctrl_scaled, ctrl_scaled_inv, ctrl_scaled_int, ctrl_scaled_frac}));

  // Basic arithmetic decomposition checks
  assert property (disable iff (!started) ctrl_scaled_int  == ctrl_scaled);
  assert property (disable iff (!started) ctrl_scaled_frac == (ctrl_scaled - ctrl_scaled_int));
  assert property (disable iff (!started) ctrl_scaled_inv  == (RATIO - ctrl_scaled));

  // Divider safety: no divide-by-zero
  assert property (disable iff (!started)
                   (ctrl_scaled_int + ctrl_scaled_frac) != '0)
    else $error("freq_synthesizer: divide-by-zero in divider calculation");

  // Divider functional relation (guard against async ctrl changes)
  assert property (disable iff (!started)
                   $stable(ctrl) |-> divider == (RATIO / (ctrl_scaled_int + ctrl_scaled_frac)));

  // Counter behavior
  assert property (disable iff (!started)
                   (counter != '0) |=> counter == $past(counter) - 1);
  assert property (disable iff (!started)
                   (counter == '0) |=> counter == $past(divider));

  // Phase accumulator gating on counter
  assert property (disable iff (!started)
                   (counter != '0) |=> phase_accumulator == $past(phase_accumulator));
  assert property (disable iff (!started)
                   (counter == '0) |=> phase_accumulator == $past(phase_accumulator_next));

  // Phase increment computation (guarded for async ctrl)
  assert property (disable iff (!started)
                   $stable(ctrl) |-> phase_increment == $past(ctrl_scaled_int + (ctrl_scaled_frac > phase_accumulator)));

  // Phase accumulator next computation
  assert property (disable iff (!started)
                   phase_accumulator_next == $past(phase_accumulator + phase_increment));

  // syn_clk toggles iff threshold reached
  assert property (disable iff (!started)
                   (phase_accumulator_next >= RATIO) |-> ##0 (syn_clk != $past(syn_clk)));
  assert property (disable iff (!started)
                   (phase_accumulator_next <  RATIO) |-> ##0 (syn_clk == $past(syn_clk)));

  // Reveal integer-fraction bug (will hold true with current integer math)
  assert property (disable iff (!started) ctrl_scaled_frac == '0)
    else $error("freq_synthesizer: fractional ctrl_scaled_frac unexpectedly non-zero");

  // Coverage
  cover property (disable iff (!started) syn_clk != $past(syn_clk));
  cover property (disable iff (!started) counter == '0);
  cover property (disable iff (!started) phase_accumulator_next >= RATIO);
  // Fractional branch ever taken? (likely never with current integer math)
  cover property (disable iff (!started) phase_increment == (ctrl_scaled_int + 1));

endmodule

bind freq_synthesizer freq_synthesizer_sva();