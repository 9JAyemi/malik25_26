// SVA for tone_generator
module tone_generator_sva;

  // Bound into tone_generator scope; directly references DUT signals
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Async + sync reset checks
  always @(posedge rst) begin
    assert (waveform == 8'h00)
      else $error("tone_generator: waveform not cleared on async reset");
  end
  ap_rst_sync: assert property (rst |-> waveform == 8'h00);

  // Mode helpers
  function automatic bit is_dtmf;  return (type == 2'b00); endfunction
  function automatic bit is_sine;  return (type == 2'b01); endfunction
  function automatic bit is_square;return (type != 2'b00) && (type != 2'b01); endfunction

  // DTMF: in-range index and output mapping
  ap_dtmf_idx_range: assert property (is_dtmf() |-> (freq[15:4] == 0));

  // Sine: counter update, waveform update and hold when inactive
  ap_sine_counter_inc:  assert property (is_sine()  |=> sine_counter == $past(sine_counter) + $past(freq));
  ap_sine_counter_hold: assert property (!is_sine() |=> sine_counter == $past(sine_counter));
  ap_sine_wave_update:  assert property (is_sine()  |=> sine_waveform == (8'sd-128 >>> ($past(sine_counter)/16'd32768)));
  ap_sine_wave_hold:    assert property (!is_sine() |=> sine_waveform == $past(sine_waveform));

  // Square: counter update, waveform update and hold when inactive
  ap_square_counter_inc:  assert property (is_square()  |=> square_counter == $past(square_counter) + $past(freq));
  ap_square_counter_hold: assert property (!is_square() |=> square_counter == $past(square_counter));
  ap_square_wave_update:  assert property (is_square()  |=> square_waveform == (($past(square_counter) >= 16'd16384) ? 8'hFF : 8'h00));
  ap_square_wave_hold:    assert property (!is_square() |=> square_waveform == $past(square_waveform));

  // Output mux consistency (final waveform uses prior-cycle selected source)
  ap_mux_consistency: assert property (
    1'b1 |=> waveform ==
      ($past(type)==2'b00 ? dtmf_waveform[$past(freq)] :
       $past(type)==2'b01 ? $past(sine_waveform) : $past(square_waveform))
  );

  // Functional coverage
  cp_reset:           cover property (rst ##1 !rst && waveform==8'h00);
  cp_dtmf_min:        cover property (is_dtmf() && (freq==16'd0));
  cp_dtmf_max:        cover property (is_dtmf() && (freq==16'd15));
  cp_sine_vals:       cover property (is_sine() ##1 (sine_waveform inside {8'h80,8'hC0}));
  cp_sine_msb_toggle: cover property (is_sine() && (sine_counter[15]==0) ##1 is_sine() && (sine_counter[15]==1));
  cp_square_0:        cover property (is_square() && square_waveform==8'h00);
  cp_square_1:        cover property (is_square() && square_waveform==8'hFF);
  cp_square_toggle:   cover property (is_square() && $changed(square_waveform));
  cp_mode_switch:     cover property (is_dtmf() ##1 is_sine() ##1 is_square());

endmodule

bind tone_generator tone_generator_sva sva();