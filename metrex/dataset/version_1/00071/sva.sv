// SVA for video_palframe
module video_palframe_sva (video_palframe dut);

  default clocking cb @(posedge dut.clk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge dut.clk) past_valid <= 1;

  function automatic logic [1:0] map3 (logic [2:0] x);
    case (x)
      3'b000: map3 = 2'b00;
      3'b001: map3 = 2'b01;
      3'b010: map3 = 2'b11;
      3'b011: map3 = 2'b10;
      3'b100: map3 = 2'b00;
      3'b101: map3 = 2'b10;
      3'b110: map3 = 2'b11;
      3'b111: map3 = 2'b01;
    endcase
  endfunction

  function automatic logic [1:0] map2 (logic [1:0] x);
    case (x)
      2'b00: map2 = 2'b00;
      2'b01: map2 = 2'b01;
      2'b10: map2 = 2'b11;
      2'b11: map2 = 2'b10;
    endcase
  endfunction

  // Structural/comb checks
  a_zxcolor:       assert property (dut.zxcolor == ((dut.hpix && dut.vpix) ? dut.pixels : (dut.border_sync_ena ? dut.synced_border : dut.border)));
  a_up_color:      assert property (dut.up_color == ((dut.hpix && dut.vpix) ? {dut.up_palsel, ~dut.up_pixel, (dut.up_pixel ? dut.up_ink : dut.up_paper)} : {3'd0, dut.border[2:0]}));
  a_palette_color: assert property (dut.palette_color == (dut.up_ena ? {3'b100, dut.up_color} : {5'd0, dut.zxcolor}));
  a_palcolor_bus:  assert property (dut.palcolor == {dut.palette_read[4:3], dut.palette_read[7:6], dut.palette_read[1:0]});

  // synced_border behavior
  a_sync_sample: assert property (past_valid && $past(dut.border_sync) |-> dut.synced_border == $past(dut.border));
  a_sync_hold:   assert property (past_valid && !$past(dut.border_sync) |-> dut.synced_border == $past(dut.synced_border));

  // vsync pipeline and edge detect
  a_vsync_r:     assert property (past_valid |-> dut.vsync_r == $past(dut.vsync));
  a_vsync_start: assert property (dut.vsync_start == (dut.vsync && !$past(dut.vsync)));

  // Counters and plus1
  a_ctr14_inc:  assert property (past_valid |-> dut.ctr_14 == $past(dut.ctr_14) + 2'b01);
  a_ctr_h:      assert property (past_valid &&  dut.hsync_start |-> dut.ctr_h == ~$past(dut.ctr_h));
  a_ctr_h_hold: assert property (past_valid && !dut.hsync_start |-> dut.ctr_h ==  $past(dut.ctr_h));
  a_ctr_v:      assert property (past_valid &&  dut.vsync_start |-> dut.ctr_v == ~$past(dut.ctr_v));
  a_ctr_v_hold: assert property (past_valid && !dut.vsync_start |-> dut.ctr_v ==  $past(dut.ctr_v));
  a_plus1:      assert property (dut.plus1 == (dut.ctr_14[1] ^ dut.ctr_h ^ dut.ctr_v));

  // Palette read/write timing
  a_palette_read_q: assert property (past_valid |-> dut.palette_read == $past(dut.palette[dut.palette_color]));
  a_pal_wr_atm:     assert property (past_valid && $past(dut.atm_palwr)
                                     |-> dut.palette[{5'd0, $past(dut.zxcolor)}]
                                         == {$past(dut.atm_paldata[3:2]),1'b0,$past(dut.atm_paldata[5:4]),1'b0,$past(dut.atm_paldata[1:0])});
  a_pal_wr_up:      assert property (past_valid && $past(dut.up_palwr) && !$past(dut.atm_palwr)
                                     |-> dut.palette[{3'b100, $past(dut.up_paladdr)}] == $past(dut.up_paldata));

  // RGB decode and output gating
  a_red_map:        assert property (dut.red == map3(dut.palette_read[7:5]));
  a_grn_map:        assert property (dut.grn == map3(dut.palette_read[4:2]));
  a_blu_map:        assert property (dut.blu == map2(dut.palette_read[1:0]));
  a_color_blank0:   assert property ((dut.hblank || dut.vblank) |-> dut.color == 6'd0);
  a_color_draw:     assert property ((!dut.hblank && !dut.vblank) |-> dut.color == {dut.grn, dut.red, dut.blu});

  // Key covers
  c_pix_core:     cover property (dut.hpix && dut.vpix && !dut.hblank && !dut.vblank);
  c_pix_border:   cover property (!dut.hpix || !dut.vpix);
  c_sync_bsample: cover property ($rose(dut.border_sync));
  c_up_sel:       cover property (dut.up_ena && dut.hpix && dut.vpix && (dut.up_pixel==1'b0) ##1 (dut.up_pixel==1'b1));
  c_pal_wr_atm:   cover property (dut.atm_palwr);
  c_pal_wr_up:    cover property (dut.up_palwr && !dut.atm_palwr);
  c_pal_wr_both:  cover property (dut.atm_palwr && dut.up_palwr);
  c_vsync:        cover property (dut.vsync_start);
  c_hsync:        cover property (dut.hsync_start);
  c_ctr14_roll:   cover property (dut.ctr_14==2'b11 ##1 dut.ctr_14==2'b00);
  c_color_nz:     cover property (!dut.hblank && !dut.vblank && dut.color != 6'd0);

endmodule

bind video_palframe video_palframe_sva sva_video_palframe();