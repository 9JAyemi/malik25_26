// Assertions for reverse_parity, shift_register, and top_module
// Bind these SVA modules after compiling the DUT.

module shift_register_sva;
  default clocking cb @(posedge clk); endclocking

  // Async reset must clear immediately (NBA-safe)
  ap_async_reset: assert property (@(posedge reset) ##0 reg_data == 3'b000);

  // Synchronous behavior at clk edge (NBA-safe sampling)
  ap_sync_reset: assert property (reset |-> ##0 reg_data == 3'b000);
  ap_load:       assert property (!reset && load   |-> ##0 reg_data == load_data);
  ap_shift:      assert property (!reset && !load |-> ##0 reg_data == { $past(reg_data[1:0]), 1'b0 });

  // Serial output is LSB tap
  ap_serial_taps_lsb: assert property (serial_out == reg_data[0]);

  // After three shifts with zeros, register must be zero
  ap_flush_3: assert property (disable iff (reset) (!load)[*3] |-> ##0 reg_data == 3'b000);

  // X checks
  ax_ld_known_when_load: assert property (load |-> !$isunknown(load_data));
  ax_ser_known:          assert property (!$isunknown(serial_out));

  // Coverage
  cv_reset:   cover property (@(posedge reset) 1);
  cv_load:    cover property (!reset && load);
  cv_shift:   cover property (!reset && !load);
  cv_flush_3: cover property (disable iff (reset) (!load)[*3]);
endmodule

bind shift_register shift_register_sva sr_sva();


module top_module_sva;
  default clocking cb @(posedge clk); endclocking

  // reverse_parity functional correctness (as seen at top-level wires)
  ap_rev_out: assert property (reverse_out_vec == {in_vec[2], in_vec[1], in_vec[0], ~^(in_vec[2:0])});
  ap_rev_par: assert property (reverse_even_parity == ^(in_vec[2:0]));
  ap_rev_consistency: assert property (reverse_out_vec[0] == ~reverse_even_parity);

  // Muxing behavior for outputs
  ap_outvec_sel1: assert property (disable iff (reset)
                                   select |-> (out_vec[3:1] == in_vec[2:0] &&
                                               out_vec[0]   == ~^(in_vec[2:0])));
  ap_outvec_sel0: assert property (disable iff (reset) !select |-> out_vec == 4'b0000);

  // Parity output behavior (note: this is odd parity by spec)
  ap_par_sel1: assert property (select  |-> (even_parity == ^(in_vec[2:0]) &&
                                             out_vec[0]  == ~even_parity));
  ap_par_sel0: assert property (!select |-> (even_parity == ^(in_vec[3:0])));

  // Serial output gating
  ap_ser_sel1: assert property (select  |-> serial_out == 1'b0);
  ap_ser_sel0: assert property (!select |-> serial_out == shift_serial_out);

  // X-propagation checks (only when inputs are known)
  ax_known_sel1: assert property (select  && !$isunknown(in_vec[2:0])
                                  |-> !$isunknown({out_vec, even_parity, serial_out}));
  ax_known_sel0: assert property (!select && !$isunknown({in_vec, shift_serial_out})
                                  |-> !$isunknown({out_vec, even_parity, serial_out}));

  // Coverage: exercise both select paths, parity cases
  cv_sel0: cover property (!select);
  cv_sel1: cover property (select);
  cv_par3_even: cover property (select  && ~^(in_vec[2:0]));
  cv_par3_odd:  cover property (select  &&  ^(in_vec[2:0]));
  cv_par4_even: cover property (!select && ~^(in_vec[3:0]));
  cv_par4_odd:  cover property (!select &&  ^(in_vec[3:0]));
endmodule

bind top_module top_module_sva top_sva();