// SVA for vga. Bind to the DUT to check counters, syncs, blanks, and coverage.
module vga_sva
  #(parameter int HMAX      = 10'd799,
               HBLANK_ON = 10'd639,
               HSYNC_ON  = 10'd655,
               HSYNC_OFF = 10'd751,
    parameter int VMAX      = 10'd523,
               VBLANK_ON = 10'd479,
               VSYNC_ON  = 10'd490,
               VSYNC_OFF = 10'd492)
(
  input  logic        vclock,
  input  logic [9:0]  hcount,
  input  logic [9:0]  vcount,
  input  logic        hsync,
  input  logic        vsync,
  input  logic        blank,
  input  logic        hblank,
  input  logic        vblank
);

  default clocking cb @(posedge vclock); endclocking

  // Counter ranges
  assert property (hcount <= HMAX);
  assert property (vcount <= VMAX);

  // Horizontal counter behavior
  assert property (hcount != HMAX |=> hcount == $past(hcount) + 10'd1);
  assert property ((hcount == HMAX) && (vcount != VMAX) |=> (hcount == 10'd0) && (vcount == $past(vcount) + 10'd1));
  assert property ((hcount == HMAX) && (vcount == VMAX) |=> (hcount == 10'd0) && (vcount == 10'd0));
  // Vertical counter only changes at end-of-line
  assert property (hcount != HMAX |=> vcount == $past(vcount));

  // hblank exact mapping: 1 for hcount >= 640
  assert property ((hcount inside {[10'd640:HMAX]}) |-> hblank);
  assert property ((hcount inside {[10'd0:HBLANK_ON]}) |-> !hblank);

  // vblank exact mapping: 1 for vcount >= 480
  assert property ((vcount inside {[10'd480:VMAX]}) |-> vblank);
  assert property ((vcount inside {[10'd0:VBLANK_ON]}) |-> !vblank);

  // hsync is low for hcount 656..751 inclusive, high otherwise (active-low)
  assert property ((hcount inside {[HSYNC_ON+10'd1:HSYNC_OFF]}) |-> !hsync);
  assert property ((hcount inside {[10'd0:HSYNC_ON], [HSYNC_OFF+10'd1:HMAX]}) |-> hsync);

  // vsync is low for lines 491..492 inclusive (active-low)
  assert property ((vcount inside {[VSYNC_ON+10'd1:VSYNC_OFF]}) |-> !vsync);
  assert property (! (vcount inside {[VSYNC_ON+10'd1:VSYNC_OFF]}) |->  vsync);

  // blank combines vblank and (hblank except at the last pixel)
  assert property (blank == (vblank || (hcount inside {[10'd640:HMAX-10'd1]})));

  // Legal toggle points only
  assert property ((hsync != $past(hsync)) |-> ($past(hcount) inside {HSYNC_ON, HSYNC_OFF}));
  assert property ((vsync != $past(vsync)) |-> ($past(hcount) == HMAX && ($past(vcount) inside {VSYNC_ON, VSYNC_OFF})));
  assert property ((hblank != $past(hblank)) |-> ($past(hcount) inside {HBLANK_ON, HMAX}));
  assert property ((vblank != $past(vblank)) |-> ($past(hcount) == HMAX && ($past(vcount) inside {VBLANK_ON, VMAX})));

  // Coverage
  cover property ((hcount == HMAX && vcount == VMAX) ##1 (hcount == 10'd0 && vcount == 10'd0)); // end-of-frame
  cover property ((hcount == HSYNC_ON+10'd1 && !hsync) ##[96] (hcount == HSYNC_OFF+10'd1 && hsync)); // hsync pulse
  cover property ((hcount == HMAX && vcount == VBLANK_ON) ##1 vblank); // vblank assertion
  cover property ((hcount == HMAX && vcount == VMAX) ##1 !vblank);     // vblank deassertion
  cover property (!vblank && (hcount == 10'd640) ##1 blank);           // blank due to hblank
  cover property ((vcount == 10'd480) && (hcount == 10'd0) && vblank && blank); // blank due to vblank

endmodule

// Bind into the DUT (connect internal regs/wires by name)
bind vga vga_sva #(
  .HMAX(10'd799), .HBLANK_ON(10'd639), .HSYNC_ON(10'd655), .HSYNC_OFF(10'd751),
  .VMAX(10'd523), .VBLANK_ON(10'd479), .VSYNC_ON(10'd490), .VSYNC_OFF(10'd492)
) vga_sva_i (
  .vclock(vclock),
  .hcount(hcount),
  .vcount(vcount),
  .hsync(hsync),
  .vsync(vsync),
  .blank(blank),
  .hblank(hblank),
  .vblank(vblank)
);