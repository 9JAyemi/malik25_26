// SVA for red_pitaya_lpf_block
// Bind this module to the DUT:  bind red_pitaya_lpf_block red_pitaya_lpf_block_sva();

module red_pitaya_lpf_block_sva;

  // The bound module is inserted in DUT scope; we can see DUT signals/params.
  // Default clock
  default clocking cb @(posedge clk_i); endclocking

  // --------------------
  // Reset behavior
  // --------------------
  // Synchronous active-low reset clears state
  a_reset_clears: assert property (!rstn_i |-> (y == '0 && delta == '0));

  // Registered state must not glitch between clocks
  a_regs_stable_between_clk: assert property (@(negedge clk_i) $stable({y, delta}));

  // --------------------
  // Combinational definitions
  // --------------------
  // y_out must equal arithmetic right-shift of y by MAXSHIFT
  a_yout_def: assert property (y_out == ($signed(y) >>> MAXSHIFT));

  // shifted_delta must implement saturated shift amount
  a_shifted_delta_def: assert property (shifted_delta == (delta <<< ((shift < MAXSHIFT) ? shift : MAXSHIFT)));

  // Output mux must match mode controls
  a_mux_map: assert property (signal_o == (filter_on ? (highpass ? delta : y_out) : signal_i));

  // --------------------
  // Sequential updates
  // --------------------
  // delta[n+1] = signal_i[n] - y_out[n]
  a_delta_update: assert property (rstn_i && $past(rstn_i) |-> delta == $past(signal_i) - $past(y_out));

  // y[n+1] = y[n] + shifted_delta[n]
  a_y_update:     assert property (rstn_i && $past(rstn_i) |-> y == $past(y) + $past(shifted_delta));

  // --------------------
  // X-propagation control
  // --------------------
  // When inputs are known, internal state/outputs must be known
  a_no_x_when_inputs_known: assert property (
    rstn_i && !$isunknown({signal_i, filter_on, highpass, shift}) |-> !$isunknown({y, delta, y_out, shifted_delta, signal_o})
  );

  // --------------------
  // Coverage
  // --------------------
  c_reset_cycle:   cover property (!rstn_i ##1 rstn_i);
  c_bypass_mode:   cover property (rstn_i && !filter_on);
  c_lowpass_mode:  cover property (rstn_i &&  filter_on && !highpass);
  c_highpass_mode: cover property (rstn_i &&  filter_on &&  highpass);
  c_shift_small:   cover property (rstn_i && (shift <  MAXSHIFT));
  c_shift_sat:     cover property (rstn_i && (shift >= MAXSHIFT));
  c_neg_values:    cover property (rstn_i && (y[$bits(y)-1] || delta[$bits(delta)-1]));
  c_delta_zero:    cover property (rstn_i && filter_on && !highpass && delta == '0);

endmodule

bind red_pitaya_lpf_block red_pitaya_lpf_block_sva();