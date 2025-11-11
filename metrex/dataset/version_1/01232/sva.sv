// SVA checker for module video
// Bind this checker to the DUT: bind video video_sva vchk();

module video_sva;

  // Access DUT scope directly via bind
  // default clock
  default clocking cb @ (posedge clock); endclocking

  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clock) past_valid <= 1'b1;

  // Counter ranges and stepping
  ap_x_range: assert property (x <= 10'd800);
  ap_y_range: assert property (y <= 10'd525);

  ap_x_step:  assert property (past_valid |-> ($past(x)!=10'd800 ? x == $past(x)+10'd1 : x == 10'd0));
  ap_y_hold:  assert property (past_valid && $past(x)!=10'd800 |-> y == $past(y));
  ap_y_step:  assert property (past_valid && $past(x)==10'd800  |-> y == ($past(y)==10'd525 ? 10'd0 : $past(y)+10'd1));

  // Syncs must match x/y windows
  ap_hs: assert property (hs == (x>=10'd656 && x<=10'd751));
  ap_vs: assert property (vs == (y>=10'd490 && y<=10'd492));

  // Derived wires and bit select
  ap_rx:      assert property (rx == x - 10'd48);
  ap_ry:      assert property (ry == y - 10'd48);
  ap_bitset:  assert property (bitset == mask[3'h7 ^ rx[3:1]]);

  // RGB mapping
  ap_rgb_fn: assert property (
    (x < 10'd640 && y < 10'd480) ?
      ((x>=10'd64 && x<10'd576 && y>=10'd48 && y<10'd432) ?
        (bitset ? (r==5'd0 && g==6'd0 && b==5'd0)
                : (r==5'h0F && g==6'h1F && b==5'h0F))
      : (r==5'h0F && g==6'h1F && b==5'h0F))
    : (r==5'd0 && g==6'd0 && b==5'd0)
  );

  // Restrict RGB to legal levels only
  ap_rgb_legal: assert property ((r==5'd0 || r==5'h0F) && (g==6'd0 || g==6'h1F) && (b==5'd0 || b==5'h0F));

  // Address and data pipeline (note truncation to 14 LSBs)
  ap_addr_nib0: assert property (past_valid && $past(rx[3:0])==4'h0 |-> addr == ({2'b10,    $past(ry[8:1]), $past(rx[8:4])})[13:0]);
  ap_addr_nib1: assert property (past_valid && $past(rx[3:0])==4'h1 |-> addr == ({5'b10110, $past(ry[8:4]), $past(rx[8:4])})[13:0]);

  ap_bit8_load: assert property (past_valid && $past(rx[3:0])==4'h1 |-> bit8 == $past(d8_chr));
  ap_attr_mask: assert property (past_valid && $past(rx[3:0])==4'hF |-> attr == $past(d8_chr) && mask == $past(bit8));

  // Holds when not written this cycle
  ap_addr_hold: assert property (past_valid && !($past(rx[3:0]) inside {4'h0,4'h1}) |-> addr == $past(addr));
  ap_bit8_hold: assert property (past_valid && $past(rx[3:0])!=4'h1 |-> bit8 == $past(bit8));
  ap_am_hold:   assert property (past_valid && $past(rx[3:0])!=4'hF |-> {attr,mask} == $past({attr,mask}));

  // No X/Z after first cycle
  ap_no_xz: assert property (past_valid |-> !$isunknown({r,g,b,hs,vs,addr,x,y,attr,bit8,mask}));

  // Coverage
  cv_x_wrap:     cover property (past_valid && $past(x)==10'd800 && x==10'd0);
  cv_y_wrap:     cover property (past_valid && $past(x)==10'd800 && $past(y)==10'd525 && y==10'd0);
  cv_hs_edges:   cover property ($rose(hs)); cover property ($fell(hs));
  cv_vs_edges:   cover property ($rose(vs)); cover property ($fell(vs));
  cv_cases:      cover property (rx[3:0]==4'h0); cover property (rx[3:0]==4'h1); cover property (rx[3:0]==4'hF);
  cv_pix_outer:  cover property ((x<10'd640 && y<10'd480) && !(x>=10'd64 && x<10'd576 && y>=10'd48 && y<10'd432));
  cv_pix_inner0: cover property ((x<10'd640 && y<10'd480) && (x>=10'd64 && x<10'd576 && y>=10'd48 && y<10'd432) && !bitset);
  cv_pix_inner1: cover property ((x<10'd640 && y<10'd480) && (x>=10'd64 && x<10'd576 && y>=10'd48 && y<10'd432) &&  bitset);
  cv_blank:      cover property (x>=10'd640 || y>=10'd480);

endmodule

bind video video_sva vchk();