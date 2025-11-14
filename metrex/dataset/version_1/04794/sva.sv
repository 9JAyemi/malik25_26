// SVA for font_display
module font_display_sva (font_display dut);
  default clocking cb @ (posedge dut.clk); endclocking

  bit started; initial started=0; always @(cb) started<=1;

  // Helpers based on previous-cycle pix_x region
  let k         = $past(dut.pix_x[8:5]);
  let exp_state = (k inside {4'h5,4'h6,4'h7,4'h8}) ? dut.SCORE :
                  (k inside {4'h9,4'ha,4'hb,4'hc}) ? dut.LOGO : dut.REGISTRATION;
  let exp_char  = (k==4'h5)?7'h47:(k==4'h6)?7'h61:(k==4'h7)?7'h6d:(k==4'h8)?7'h65:
                  (k==4'h9)?7'h00:(k==4'ha)?7'h4f:(k==4'hb)?7'h76:(k==4'hc)?7'h65:7'h72;
  let exp_trgb  = (k inside {4'h5,4'h6,4'h7,4'h8}) ? 3'b001 :
                  (k==4'h9) ? 3'b110 :
                  (k inside {4'ha,4'hb,4'hc}) ? 3'b011 : 3'b001;

  // One-cycle decode and register updates from pix inputs
  assert property (disable iff (!started)
    1 |-> (dut.state_reg==exp_state &&
           dut.char_addr_reg==exp_char &&
           dut.text_rgb_reg==exp_trgb &&
           dut.row_addr_reg==$past(dut.pix_y[5:2]) &&
           dut.bit_addr_reg==$past(dut.pix_x[4:2])));

  // Pixel low-bit pipeline
  assert property (disable iff (!started) dut.row_reg==$past(dut.pix_y[1:0]));
  assert property (disable iff (!started) dut.bit_reg==$past(dut.pix_x[1:0]));

  // Output mux correctness
  assert property (dut.char_addr==dut.char_addr_reg);
  assert property (dut.text_on[3:2]==2'b00 && dut.text_on[1:0]==dut.state_reg);

  let row_sum_low4 = (dut.row_reg + (dut.char_addr_reg<<2))[3:0];

  assert property (dut.state_reg==dut.IDLE |-> (dut.row_addr==dut.row_addr_reg &&
                                                dut.bit_addr==dut.bit_addr_reg &&
                                                dut.text_rgb==dut.text_rgb_reg));

  assert property (dut.state_reg==dut.REGISTRATION |-> (dut.row_addr==dut.row_addr_reg &&
                                                        dut.bit_addr==dut.bit_addr_reg &&
                                                        dut.text_rgb==dut.text_rgb_reg));

  assert property (dut.state_reg==dut.SCORE |-> (dut.row_addr==row_sum_low4 &&
                                                 dut.bit_addr==dut.bit_reg &&
                                                 dut.text_rgb==dut.text_rgb_reg));

  assert property (dut.state_reg==dut.LOGO |-> (dut.row_addr==row_sum_low4 &&
                                                dut.bit_addr==dut.bit_reg &&
                                                dut.text_rgb==(dut.font_word[dut.bit_reg] ? dut.text_rgb_reg : 3'b110)));

  // Knownness after first cycle
  assert property (disable iff (!started) !$isunknown({dut.state_reg,dut.char_addr_reg,dut.row_addr_reg,dut.bit_addr_reg,dut.text_rgb_reg}));
  assert property (disable iff (!started) !$isunknown({dut.text_on,dut.char_addr,dut.row_addr,dut.bit_addr,dut.text_rgb}));

  // Unused control inputs do not affect registered state if pix inputs are stable
  assert property (disable iff (!started)
    ($changed(dut.score_on) && $stable({dut.pix_x,dut.pix_y})) |=> $stable({dut.state_reg,dut.char_addr_reg,dut.row_addr_reg,dut.bit_addr_reg,dut.text_rgb_reg}));
  assert property (disable iff (!started)
    ($changed(dut.logo_on) && $stable({dut.pix_x,dut.pix_y})) |=> $stable({dut.state_reg,dut.char_addr_reg,dut.row_addr_reg,dut.bit_addr_reg,dut.text_rgb_reg}));
  assert property (disable iff (!started)
    ($changed(dut.registration_on) && $stable({dut.pix_x,dut.pix_y})) |=> $stable({dut.state_reg,dut.char_addr_reg,dut.row_addr_reg,dut.bit_addr_reg,dut.text_rgb_reg}));

  // Coverage
  cover property (dut.state_reg==dut.SCORE);
  cover property (dut.state_reg==dut.LOGO);
  cover property (dut.state_reg==dut.REGISTRATION);
  cover property (dut.state_reg==dut.IDLE);

  cover property ((dut.state_reg==dut.SCORE) ##1 (dut.state_reg==dut.LOGO));
  cover property ((dut.state_reg==dut.LOGO) ##1 (dut.state_reg==dut.REGISTRATION));
  cover property ((dut.state_reg==dut.REGISTRATION) ##1 (dut.state_reg==dut.SCORE));

  cover property (dut.char_addr_reg==7'h47);
  cover property (dut.char_addr_reg==7'h61);
  cover property (dut.char_addr_reg==7'h6d);
  cover property (dut.char_addr_reg==7'h65);
  cover property (dut.char_addr_reg==7'h00);
  cover property (dut.char_addr_reg==7'h4f);
  cover property (dut.char_addr_reg==7'h76);
  cover property (dut.char_addr_reg==7'h72);

  cover property (dut.state_reg==dut.LOGO && dut.font_word[dut.bit_reg] && dut.text_rgb==dut.text_rgb_reg);
  cover property (dut.state_reg==dut.LOGO && !dut.font_word[dut.bit_reg] && dut.text_rgb==3'b110);
endmodule

bind font_display font_display_sva sva_font_display(.dut);