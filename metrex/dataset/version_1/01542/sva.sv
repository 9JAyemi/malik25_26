// SVA for tone_generator
// Bind this module to the DUT to check internal behavior.

module tone_generator_sva (
  input  logic        clk,
  input  logic [2:0]  octave,
  input  logic [8:0]  freq,
  input  logic        out,
  input  logic        pulseout,
  input  logic [7:0]  fcounter,
  input  logic [7:0]  count,
  input  logic        pulse,
  input  logic [8:0]  cfinal
);

  default clocking cb @(posedge clk); endclocking
  default disable iff ($initstate);

  // Sanity: no X on key signals
  ap_known:      assert property (!$isunknown({octave, freq, fcounter, count, pulse, cfinal, out, pulseout}));

  // fcounter mapping per octave
  ap_f0: assert property (octave==3'd0 |-> fcounter==8'd255);
  ap_f1: assert property (octave==3'd1 |-> fcounter==8'd127);
  ap_f2: assert property (octave==3'd2 |-> fcounter==8'd63 );
  ap_f3: assert property (octave==3'd3 |-> fcounter==8'd31 );
  ap_f4: assert property (octave==3'd4 |-> fcounter==8'd15 );
  ap_f5: assert property (octave==3'd5 |-> fcounter==8'd7  );
  ap_f6: assert property (octave==3'd6 |-> fcounter==8'd3  );
  ap_f7: assert property (octave==3'd7 |-> fcounter==8'd1  );

  // pulse definition
  ap_pulse_def:  assert property (pulse == (count == fcounter));

  // count update semantics
  ap_cnt_wrap:   assert property ($past(count)==$past(fcounter)  |=> count==8'd0);
  ap_cnt_inc:    assert property ($past(count)!=$past(fcounter)  |=> count==($past(count)+8'd1));

  // cfinal update semantics
  ap_cfn_hold:   assert property (!$past(pulse)                                  |=> cfinal==$past(cfinal));
  ap_cfn_inc:    assert property ( $past(pulse) && $past(cfinal)!=$past(freq)    |=> cfinal==$past(cfinal)+9'd1);
  ap_cfn_rst:    assert property ( $past(pulse) && $past(cfinal)==$past(freq)    |=> cfinal==9'd0);

  // out behavior (toggle only on pulse && cfinal==freq)
  ap_out_on:     assert property ($past(pulse) && $past(cfinal)==$past(freq)     |=> out!=$past(out));
  ap_out_off:    assert property (!($past(pulse) && $past(cfinal)==$past(freq))  |=> out==$past(out));

  // pulseout definition and effect
  ap_pout_def:   assert property (pulseout == (pulse && (cfinal==freq)));
  ap_pout_to_out:assert property (pulseout |=> out!=$past(out));

  // Optional: initial values observed on first active edge
  ap_init:       assert property ($fell($initstate) |-> out==1'b0 && count==8'd0 && cfinal==9'd0);

  // Coverage
  // - See a pulse (wrap) in each octave
  cv_oct0: cover property (octave==3'd0 && pulse);
  cv_oct1: cover property (octave==3'd1 && pulse);
  cv_oct2: cover property (octave==3'd2 && pulse);
  cv_oct3: cover property (octave==3'd3 && pulse);
  cv_oct4: cover property (octave==3'd4 && pulse);
  cv_oct5: cover property (octave==3'd5 && pulse);
  cv_oct6: cover property (octave==3'd6 && pulse);
  cv_oct7: cover property (octave==3'd7 && pulse);

  // - Observe an output toggle and a hit event
  cv_out_toggle: cover property ($changed(out));
  cv_hit_event:  cover property (pulse && (cfinal==freq));
  cv_pulseout:   cover property (pulseout);

  // - Boundary freq coverage
  cv_freq0:   cover property (freq==9'd0   && pulse && cfinal==freq);
  cv_freqmax: cover property (freq==9'd511 && pulse && cfinal==freq);

endmodule

// Bind into DUT (place in a package or a top-level include)
bind tone_generator tone_generator_sva sva_i (
  .clk(clk),
  .octave(octave),
  .freq(freq),
  .out(out),
  .pulseout(pulseout),
  .fcounter(fcounter),
  .count(count),
  .pulse(pulse),
  .cfinal(cfinal)
);