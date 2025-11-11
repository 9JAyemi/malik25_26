// SVA for dc_filter. Bind this to the DUT.
// Focus: latency, enable selection, data/valid pipelines, dc_offset feedback, X-safety, key coverage.

module dc_filter_sva;
  default clocking cb @(posedge clk); endclocking

  // X-safety
  assert property (!$isunknown({valid, dcfilt_enb}));
  assert property (valid |-> !$isunknown({data, dcfilt_offset}));
  assert property (valid_out |-> !$isunknown(data_out));

  // Valid pipeline and alignment
  assert property (valid_d   == $past(valid,   1, 0));
  assert property (valid_2d  == $past(valid_d,1, 0));
  assert property (valid_out == valid_2d);
  assert property (valid_out == $past(valid, 2, 0));

  // Data pipeline
  assert property (valid     |=> data_d  == $past(data + dcfilt_offset));
  assert property (!valid    |=> data_d  == $past(data_d)); // hold when not valid
  assert property (data_2d   == $past(data_d));
  // DC-filtered sample generation
  assert property (data_dcfilt == ($past(data_d) - $past(dc_offset_s[32:17])));
  // Output select based on enable (same-cycle enable chooses next-cycle data_out)
  assert property (!$isunknown(dcfilt_enb));
  assert property (data_out == $past(dcfilt_enb ? data_dcfilt : data_2d));

  // DC offset feedback chain
  assert property (dc_offset   == $past(dc_offset_d));
  assert property (dc_offset_d == $past(dc_offset_s));
  // Ensure slice used for subtraction is known when output is valid
  assert property (valid_out |-> !$isunknown($past(dc_offset_s[32:17])));

  // Coverage
  cover property (valid ##1 valid_d ##1 valid_2d ##1 valid_out);               // latency pipeline exercised
  cover property (dcfilt_enb && valid_out);                                    // filtered path used
  cover property (!dcfilt_enb && valid_out);                                   // bypass path used
  cover property (dcfilt_enb ##1 !dcfilt_enb ##1 dcfilt_enb);                  // enable toggling
  cover property (valid && (data == 16'h8000 || data == 16'h7fff));            // input extremes
  cover property (valid && (dcfilt_offset == 16'h8000 || dcfilt_offset == 16'h7fff));
endmodule

bind dc_filter dc_filter_sva sva_dc_filter_i();