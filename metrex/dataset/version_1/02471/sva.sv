// Bind this SVA module to the DUT
bind pixel pixel_sva p_pixel_sva();

module pixel_sva;

  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Recompute DUT combinational intents
  let blink_bit_l   = attcode[7];
  let bg_red_l      = attcode[6];
  let bg_green_l    = attcode[5];
  let bg_blue_l     = attcode[4];
  let inten_bit_l   = attcode[3];
  let fg_red_l      = attcode[2];
  let fg_green_l    = attcode[1];
  let fg_blue_l     = attcode[0];

  let foreground_l  = pixel & ~(blink_bit_l & blink);
  let intensify_l   = foreground_l & inten_bit_l;

  let red_l         = foreground_l ? fg_red_l   : bg_red_l;
  let green_l       = foreground_l ? fg_green_l : bg_green_l;
  let blue_l        = foreground_l ? fg_blue_l  : bg_blue_l;

  let past_inputs_known = !$isunknown($past({attcode,pixel,blank,hsync_in,vsync_in,blink}));

  // Update on pixclk==1: outputs match expected next cycle
  property p_update;
    past_valid && past_inputs_known && $past(pixclk) |->
      ( hsync == $past(hsync_in)
     && vsync == $past(vsync_in)
     && r[2] == ($past(blank) & $past(red_l))
     && r[1] == ($past(blank) & $past(intensify_l))
     && r[0] == ($past(blank) & $past(red_l) & $past(intensify_l))
     && g[2] == ($past(blank) & $past(green_l))
     && g[1] == ($past(blank) & $past(intensify_l))
     && g[0] == ($past(blank) & $past(green_l) & $past(intensify_l))
     && b[2] == ($past(blank) & $past(blue_l))
     && b[1] == ($past(blank) & $past(intensify_l))
     && b[0] == ($past(blank) & $past(blue_l) & $past(intensify_l)) );
  endproperty
  assert property (p_update);

  // Hold when pixclk==0: outputs retain previous values
  property p_hold;
    past_valid && !$past(pixclk) |->
      ( hsync == $past(hsync)
     && vsync == $past(vsync)
     && r == $past(r)
     && g == $past(g)
     && b == $past(b) );
  endproperty
  assert property (p_hold);

  // Blanking forces zero RGB when updating
  property p_blank_zero;
    past_valid && $past(pixclk) && !$past(blank) |->
      (r == 3'b000 && g == 3'b000 && b == 3'b000);
  endproperty
  assert property (p_blank_zero);

  // Outputs are known on update
  property p_outputs_known_on_update;
    past_valid && $past(pixclk) |->
      !$isunknown({hsync,vsync,r,g,b});
  endproperty
  assert property (p_outputs_known_on_update);

  // Functional coverage (concise but covers key modes)
  cover property (past_valid && $past(pixclk) && $past(blank) && $past(foreground_l) && $past(intensify_l)); // FG + intensify
  cover property (past_valid && $past(pixclk) && $past(blank) && !$past(foreground_l));                      // BG path
  cover property (past_valid && $past(pixclk) && !$past(blank));                                             // Blanked
  cover property (past_valid && !$past(pixclk));                                                             // Hold cycle
  cover property (past_valid && $past(pixclk) && $past(pixel) && $past(attcode[7]) && $past(blink) && !$past(foreground_l)); // Blink suppress

endmodule