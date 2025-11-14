// SVA for DSPCalcModule
// Bind as: bind DSPCalcModule DSPCalcModule_sva sva();

module DSPCalcModule_sva;

  // Access DUT scope directly via bind
  default clocking cb @(posedge clk); endclocking
  bit past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;
  default disable iff(!past_valid);

  // Datapath pipeline checks
  assert property (chargeA == $past(charge_in));
  assert property (DSPtemp == $signed($past(chargeA)) * $signed($past(signal_in)));
  assert property (DSPout  == $past(DSPtemp) + {{11{1'b0}}, $past(delayed), 12'b0}); // zero-extend shifted delayed
  assert property (pout    == $past(DSPout[26:12]));
  assert property (DSPoflow == ((~&DSPout[37:26]) && (~&(~DSPout[37:26]))));

  // j counter next-state
  assert property ( j ==
                    ( !$past(store_strb) ? 8 :
                      ( $past(bunch_strb) ? 0 : $past(j)+1 ) ) );

  // Delay line
  assert property (delayed   == $past(delayed_a));
  assert property (delayed_a ==
                   ( !$past(store_strb) ? 15'sd0 :
                     ( $past(delay_en) && ($past(j)==6) ) ? $past(pout) :
                     $past(delayed_a) ));

  // fb_cond
  assert property (fb_cond == ($past(fb_en) && (($past(j)==2) || ($past(j)==3))));

  // Edge detect and DAC clocking chain
  assert property (delay_store_strb == $past(store_strb));
  assert property (delay_clr_dac    == $past(clr_dac));
  assert property (clr_dac          == ($past(delay_store_strb) && !$past(store_strb)));
  assert property (dac_clk == ($past(fb_en) &&
                              ( ($past(j)==6) || ($past(j)==7) ||
                                $past(clr_dac) || $past(delay_clr_dac) )));

  // Key coverage
  cover property (DSPoflow);
  cover property (!DSPoflow);
  cover property ($past(store_strb) && $past(delay_en) && ($past(j)==6) && (delayed_a == $past(pout)));
  cover property (fb_cond);
  cover property ($past(fb_en) && ($past(j)==6) && dac_clk);
  cover property ($past(fb_en) && ($past(j)==7) && dac_clk);
  cover property ($past(fb_en) && $past(clr_dac)        && dac_clk);
  cover property ($past(fb_en) && $past(delay_clr_dac)  && dac_clk);
  cover property ($past(store_strb) &&  $past(bunch_strb) && (j==0));
  cover property ($past(store_strb) && !$past(bunch_strb) && (j==2));
  cover property ($past(store_strb) && !$past(bunch_strb) && (j==3));
  cover property ($past(store_strb) && !$past(bunch_strb) && (j==6));
  cover property ($past(store_strb) && !$past(bunch_strb) && (j==7));
  cover property (!$past(store_strb) && (j==8));

endmodule