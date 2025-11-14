// SVA for CDR — concise, high-signal-coverage, bindable
// Focus: pipeline correctness, filter/vco recursions, comb mappings, sign handling, X-safety, coverage

bind CDR CDR_sva u_cdr_sva();

module CDR_sva;

  // Clocking and initialization guard for $past
  bit init1, init2;
  always @(posedge ref_clk) begin
    init1 <= 1'b1;
    init2 <= init1;
  end

  default clocking cb @(posedge ref_clk); endclocking
  default disable iff (!init2);

  // X-safety on sampled inputs
  assert property (!$isunknown(ref_clk) && !$isunknown(data))
    else $error("CDR: X/Z on inputs at ref_clk edge");

  // Sampling flops
  assert property (data_reg    == $past(data))
    else $error("CDR: data_reg must sample previous data");
  assert property (ref_clk_reg == $past(ref_clk))
    else $error("CDR: ref_clk_reg must sample previous ref_clk");

  // Phase detector shift/registering
  assert property (phase_error[1] == $past(phase_error[0]))
    else $error("CDR: phase_error shift MSB mismatch");
  assert property (phase_error[0] == $past(data_reg ^ ref_clk_reg))
    else $error("CDR: phase_error LSB must be prior data^ref_clk");
  assert property (phase_error_sign == phase_error[1])
    else $error("CDR: phase_error_sign must mirror phase_error[1]");

  // Comb mappings
  // vco_in is a wire to filter_out
  assert property (vco_in == filter_out)
    else $error("CDR: vco_in must equal filter_out");
  // clk_out mirrors vco_out[31] at all times
  always @* assert (clk_out === vco_out[31])
    else $error("CDR: clk_out must equal vco_out[31]");

  // One-pole filter update (exact RTL recurrence)
  assert property (filter_out == $past(filter_out) +
                   (($past(filter_in) - $past(filter_out)) >> 4))
    else $error("CDR: filter_out update mismatch");

  // VCO update (exact RTL recurrence)
  assert property (vco_out == $past(vco_out) +
                   (($past(vco_in) - $past(vco_out)) >> 8))
    else $error("CDR: vco_out update mismatch");

  // Intent check: sign consistency for filter_in (flags width/sign bugs)
  // When phase_error_sign is 1 and phase_error != 0, filter_in should be negative
  assert property ((phase_error_sign && (phase_error != 2'b00)) |-> ($signed(filter_in) < 0))
    else $error("CDR: filter_in sign not negative when phase_error_sign==1 (possible zero-extension bug)");
  // When phase_error_sign is 0, filter_in should be non-negative
  assert property ((!phase_error_sign) |-> ($signed(filter_in) >= 0))
    else $error("CDR: filter_in negative while phase_error_sign==0");

  // Basic functional coverage
  cover property (phase_error == 2'b01);
  cover property (phase_error == 2'b10);
  cover property (phase_error_sign == 1'b0);
  cover property (phase_error_sign == 1'b1);
  cover property ($changed(filter_out));
  cover property ($past(filter_out) < filter_out); // filter rising
  cover property ($past(filter_out) > filter_out); // filter falling
  cover property ($rose(vco_out[31]));
  cover property ($fell(vco_out[31]));
  cover property (($signed(filter_in) < 0));
  cover property (($signed(filter_in) >= 0));

endmodule