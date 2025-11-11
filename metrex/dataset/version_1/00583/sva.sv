// SystemVerilog Assertions for speaker_iface
// Bind into the DUT to access internals without changing RTL

module speaker_iface_sva;

  default clocking cb @(posedge clk_i); endclocking
  default disable iff (rst_i);

  // Helpers
  let lr_edge = (fBCLK_HL && (bDACLRCK != bDACLRCK_old));        // LRCK toggled on this BCLK pulse
  let no_lr   = (fBCLK_HL && (bDACLRCK == bDACLRCK_old));        // No LRCK toggle on this BCLK pulse

  // Reset behavior (only signals explicitly reset in RTL)
  assert property ($rose(rst_i) |-> ##1 (!fBCLK_HL && !bCurrentClk && !bFilterClk1 && !bFilterClk2));

  // BCLK input 2-flop filter behavior
  assert property ($stable(aud_bclk_i) |=> (bFilterClk1 == aud_bclk_i) && (bFilterClk2 == $past(aud_bclk_i)));
  assert property ((bFilterClk1==bFilterClk2) && (bCurrentClk != bFilterClk2) |=> bCurrentClk == $past(bFilterClk2));

  // fBCLK_HL pulse: one-cycle wide, created on filtered high->low only
  assert property (fBCLK_HL |=> !fBCLK_HL);
  assert property ((bFilterClk1==bFilterClk2) && ($past(bCurrentClk)==1) && ($past(bCurrentClk)!=bFilterClk2) |=> fBCLK_HL);

  // LRCK sampling and capture
  assert property (bDACLRCK == $past(aud_daclrck_i));
  assert property (fBCLK_HL |=> bDACLRCK_old == $past(bDACLRCK));

  // Actions on LRCK edge (load DAC, start ADC, route previous ADC to outputs, set ready)
  assert property (lr_edge |=> 
      (rDAC == ($past(bDACLRCK) ? $past(datar_i) : $past(datal_i))) &&
      (aud_dacdat_o == 1'b0) &&
      (fADCReady == 1'b0) &&
      (rADC == 16'h0001) &&
      (ready_o == ~$past(bDACLRCK)) &&
      ($past(bDACLRCK) ? (datal_o == $past(rADC)) : (datar_o == $past(rADC)))
  );

  // Shifts on BCLK when no LRCK edge
  assert property (no_lr |=> 
      (rDAC == {$past(rDAC[14:0]), 1'b0}) &&
      (aud_dacdat_o == $past(rDAC[15]))
  );

  // ADC shift/ready machine
  assert property (no_lr && !$past(fADCReady) |=> 
      (fADCReady == $past(rADC[15])) &&
      (rADC == {$past(rADC[14:0]), aud_adcdat_i})
  );
  assert property (no_lr &&  $past(fADCReady) |=> 
      (fADCReady == 1'b1) && (rADC == $past(rADC))
  );

  // ready_o origin and clearing
  assert property ($rose(ready_o) |-> $past(lr_edge) && (ready_o == ~$past(bDACLRCK)));
  assert property (!fBCLK_HL && $past(ready_o) |=> !ready_o);

  // Stability when no BCLK pulse
  assert property (!fBCLK_HL |=> $stable(rDAC) && $stable(rADC) && $stable(fADCReady) && $stable(aud_dacdat_o));

  // Coverage
  cover property ($rose(ready_o) && $past(bDACLRCK)==1); // left sample ready
  cover property ($rose(ready_o) && $past(bDACLRCK)==0); // right sample ready
  cover property ($rose(fADCReady));                     // ADC word completed

endmodule

bind speaker_iface speaker_iface_sva sva();