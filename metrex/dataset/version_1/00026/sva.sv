// SVA for module bluetooth
// Bind these assertions into the DUT
bind bluetooth bluetooth_sva #( .n(n),
                                .MODULATION_SCHEME(MODULATION_SCHEME),
                                .FHSS_ENABLED(FHSS_ENABLED),
                                .FHSS_PATTERN(FHSS_PATTERN),
                                .DFE_ENABLED(DFE_ENABLED) );

module bluetooth_sva #(parameter int n = 8,
                       parameter string MODULATION_SCHEME = "GFSK",
                       parameter bit FHSS_ENABLED = 1,
                       parameter string FHSS_PATTERN = "10101010",
                       parameter bit DFE_ENABLED = 1) ();
  // Inside bind scope, we can directly see DUT signals/regs
  // clk, rst, in, out, bt_in, bt_out, data, bt_out_reg, bt_in_reg, out_reg

  // Static/structural checks
  initial begin
    assert (n % 2 == 0)
      else $error("bluetooth: n must be even to avoid i+1 out-of-bounds");
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset behavior
  ap_reset_clear: assert property (rst |=> (bt_out_reg == 8'h00 && bt_in_reg == 8'h00 && out_reg == '0));

  // Data pipeline (NBL) capture
  ap_data_lat:   assert property (data == $past(in));

  // Width/truncation awareness
  ap_bt_out_lsb: assert property (bt_out == bt_out_reg[0]);

  // FHSS behavior (as coded: last nonblocking assignment wins; rotate-by-1 of previous value)
  // Transmitter: final bt_out_reg ignores new modulation in this cycle when FHSS is enabled and rotates previous value once.
  ap_tx_fhss_rot: assert property (FHSS_ENABLED |-> bt_out_reg == {$past(bt_out_reg[6:0]), $past(bt_out_reg[7])});
  // And bt_out LSB equals previous MSB
  ap_tx_bt_out_from_prev_msb: assert property (FHSS_ENABLED |-> bt_out == $past(bt_out_reg[7]));

  // If FHSS disabled, tx bits reflect last i==n-2 mapping (uses previous data due to NBL)
  // Pair pattern: for all j even, {j}=data[n-2]^data[n-1], {j+1}=data[n-1]
  genvar jj;
  generate
    for (jj = 0; jj < 8; jj += 2) begin : g_tx_no_fhss_bits
      ap_tx_no_fhss_even: assert property (!FHSS_ENABLED |-> bt_out_reg[jj]   == ($past(data[n-2]) ^ $past(data[n-1])));
      ap_tx_no_fhss_odd:  assert property (!FHSS_ENABLED |-> bt_out_reg[jj+1] ==  $past(data[n-1]));
    end
  endgenerate

  // Receiver FHSS behavior (as coded: final bt_in_reg rotates previous value once when enabled)
  ap_rx_fhss_rot: assert property (FHSS_ENABLED |-> bt_in_reg == {$past(bt_in_reg[6:0]), $past(bt_in_reg[7])});
  // If FHSS disabled, capture from bt_in (1-bit extended)
  ap_rx_no_fhss_cap: assert property ((!FHSS_ENABLED) |-> bt_in_reg == {7'b0, $past(bt_in)});

  // Receiver demod when DFE disabled (as coded: uses previous bt_in_reg, last j==6 dominates)
  generate
    genvar ii;
    for (ii = 0; ii < n; ii += 2) begin : g_rx_demod_no_dfe
      ap_rx_no_dfe_even: assert property ((!DFE_ENABLED) |-> out[ii]   == ($past(bt_in_reg[6]) ^ $past(bt_in_reg[7])));
      ap_rx_no_dfe_odd:  assert property ((!DFE_ENABLED) |-> out[ii+1] ==  $past(bt_in_reg[7]));
    end
  endgenerate

  // Receiver DFE enabled: output only changes if tapped bits were 1 in previous cycle
  ap_dfe_change_needs_taps: assert property (DFE_ENABLED && (out != $past(out)) |-> $past(bt_in_reg[6] | bt_in_reg[7] | bt_in_reg[0]));
  ap_dfe_stable_when_no_taps: assert property (DFE_ENABLED && ($past(bt_in_reg[6] | bt_in_reg[7] | bt_in_reg[0]) == 1'b0) |-> out == $past(out));

  // Coverage
  cv_reset_seq:       cover property (rst ##1 !rst);
  cv_bt_out_toggle:   cover property (!rst and $changed(bt_out));
  cv_tx_fhss_effect:  cover property (FHSS_ENABLED and bt_out == $past(bt_out_reg[7]));
  cv_dfe_effect:      cover property (DFE_ENABLED and $past(bt_in_reg[6] | bt_in_reg[7] | bt_in_reg[0]) and (out != $past(out)));
endmodule