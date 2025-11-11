// SVA for shift_register and roi
// Bind into DUTs to access internal signals directly.

module shift_register_sva;
  // Access bound instance signals: clk, stb, di, do, din, dout, din_shr, dout_shr, DIN_N, DOUT_N
  default clocking cb @(posedge clk); endclocking
  default disable iff ($initstate);

  // Inputs should not be X/Z at the sampling edge
  a_no_x_inputs: assert property (!$isunknown({stb, di}));

  // Core shift behavior
  a_din_shift: assert property (
    (!$isunknown($past({din_shr, di}))) |->
      din_shr == { $past(din_shr[DIN_N-2:0]), $past(di) }
  );

  a_dout_shift: assert property (
    (!$isunknown($past({dout_shr, din_shr[DIN_N-1]}))) |->
      dout_shr == { $past(dout_shr[DOUT_N-2:0]), $past(din_shr[DIN_N-1]) }
  );

  // Capture on stb
  a_capture_on_stb: assert property (
    stb && !$isunknown($past({din_shr, dout_shr})) |=> 
      (din == $past(din_shr)) && (dout == $past(dout_shr)) && (do == $past(dout_shr))
  );

  // Hold when !stb
  a_hold_when_not_stb: assert property (
    !stb |=> (din == $past(din)) && (dout == $past(dout)) && (do == $past(do))
  );

  // Output mapping
  a_do_maps_dout: assert property (do == dout);

  // Coverage
  c_stb_pulse:         cover property (stb);
  c_back_to_back_caps: cover property (stb ##1 !stb ##1 stb);
  c_msb_to_lsb_xfer:   cover property ($rose(din_shr[DIN_N-1]) ##1 (dout_shr[0] == 1'b1));
endmodule

bind shift_register shift_register_sva svas_shift_register();

// SVA for simple ROI AND gate
module roi_sva;
  // Clockless concurrent assertion for pure combinational function
  a_and_func: assert property (o0 == (ci & s0));
  c_o0_0:     cover property (!o0);
  c_o0_1:     cover property (o0);
endmodule

bind roi roi_sva svas_roi();