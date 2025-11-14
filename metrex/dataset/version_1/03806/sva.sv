// SVA for modulator. Bind this file to the DUT.
module modulator_sva;

  // Access DUT signals via bind scope
  // Clocks
  bit past_pos, past_neg;
  initial begin past_pos = 1'b0; past_neg = 1'b0; end
  always @(posedge adc_clk) past_pos <= 1'b1;
  always @(negedge adc_clk) past_neg <= 1'b1;

  default clocking cb @(posedge adc_clk or negedge adc_clk); endclocking

  // Sanity: no X/Z on outputs
  assert property ( !$isunknown({ssp_frame, ssp_din, modulating_carrier, pwr_oe1, pwr_oe3, pwr_oe4}) );

  // Synchronizer: ssp_din samples after_hysteresis on posedge
  assert property (@(posedge adc_clk) past_pos |-> ssp_din == $past(after_hysteresis));

  // Combinational mapping of modulating_carrier per mod_type
  assert property ( (mod_type==4'b0000) |-> (modulating_carrier==1'b0) );
  assert property ( (mod_type==4'b0001) |-> (modulating_carrier==(ssp_din ^ ssp_clk_divider[3])) );
  assert property ( (mod_type==4'b0100) |-> (modulating_carrier==(ssp_din & ssp_clk_divider[5])) );
  assert property ( ((mod_type==4'b0101)||(mod_type==4'b0110)) |-> (modulating_carrier==(ssp_din & ssp_clk_divider[4])) );
  assert property ( (!(mod_type inside {4'b0000,4'b0001,4'b0100,4'b0101,4'b0110})) |-> (modulating_carrier==1'b0) );

  // Power outputs
  assert property ( pwr_oe1==1'b0 );
  assert property ( pwr_oe3==1'b0 );
  assert property ( pwr_oe4==modulating_carrier );

  // ssp_frame updates on negedge adc_clk based on divider window and mod_type
  // Check effect of last negedge at the next posedge (avoids NBA sampling issues)
  assert property (@(posedge adc_clk)
                   past_neg && $past((mod_type==4'b0100) && (ssp_clk_divider[8:5]==4'b0001),1,negedge adc_clk) |-> (ssp_frame==1'b1) );
  assert property (@(posedge adc_clk)
                   past_neg && $past((mod_type==4'b0100) && (ssp_clk_divider[8:5]==4'b0101),1,negedge adc_clk) |-> (ssp_frame==1'b0) );
  assert property (@(posedge adc_clk)
                   past_neg && $past((mod_type!=4'b0100) && (ssp_clk_divider[7:4]==4'b0001),1,negedge adc_clk) |-> (ssp_frame==1'b1) );
  assert property (@(posedge adc_clk)
                   past_neg && $past((mod_type!=4'b0100) && (ssp_clk_divider[7:4]==4'b0101),1,negedge adc_clk) |-> (ssp_frame==1'b0) );

  // Coverage
  cover property (@(posedge adc_clk) (mod_type==4'b0000) && (modulating_carrier==1'b0));
  cover property (@(posedge adc_clk) (mod_type==4'b0001) && $changed(modulating_carrier));
  cover property (@(posedge adc_clk) (mod_type==4'b0100) && $changed(modulating_carrier));
  cover property (@(posedge adc_clk) (mod_type==4'b0101) && $changed(modulating_carrier));
  cover property (@(posedge adc_clk) (mod_type==4'b0110) && $changed(modulating_carrier));

  cover property (@(negedge adc_clk) (mod_type==4'b0100) && (ssp_clk_divider[8:5]==4'b0001));
  cover property (@(negedge adc_clk) (mod_type==4'b0100) && (ssp_clk_divider[8:5]==4'b0101));
  cover property (@(negedge adc_clk) (mod_type!=4'b0100) && (ssp_clk_divider[7:4]==4'b0001));
  cover property (@(negedge adc_clk) (mod_type!=4'b0100) && (ssp_clk_divider[7:4]==4'b0101));

  cover property (@(posedge adc_clk) $changed(pwr_oe4));

endmodule

bind modulator modulator_sva sva_modulator();