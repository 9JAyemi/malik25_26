// SVA for vga_controller
// Bind these assertions to the DUT. Focused, high-quality checks and coverage.

module vga_controller_sva (
  input logic         vclock,
  input logic [10:0]  hcount,
  input logic [9:0]   vcount,
  input logic         vsync,
  input logic         hsync,
  input logic         blank,
  input logic         hblank,
  input logic         vblank,
  input logic         hblankon,
  input logic         hsyncon,
  input logic         hsyncoff,
  input logic         hreset,
  input logic         vblankon,
  input logic         vsyncon,
  input logic         vsyncoff,
  input logic         vreset,
  input logic         next_hblank,
  input logic         next_vblank
);

  localparam int H_VISIBLE = 800;
  localparam int H_TOTAL   = 1056;
  localparam int HS_ON     = 839;
  localparam int HS_OFF    = 967;

  localparam int V_VISIBLE = 600;
  localparam int V_TOTAL   = 628;
  localparam int VS_ON     = 600;
  localparam int VS_OFF    = 604;

  logic past_valid;
  always_ff @(posedge vclock) past_valid <= 1'b1;
  default clocking cb @(posedge vclock); endclocking

  // Ranges
  assert property (past_valid |-> hcount <= H_TOTAL-1);
  assert property (past_valid |-> vcount <= V_TOTAL-1);

  // Decodes
  assert property (hblankon == (hcount == H_VISIBLE-1));
  assert property (hsyncon  == (hcount == HS_ON));
  assert property (hsyncoff == (hcount == HS_OFF));
  assert property (hreset   == (hcount == H_TOTAL-1));

  assert property (vblankon == (hreset && (vcount == V_VISIBLE-1)));
  assert property (vsyncon  == (hreset && (vcount == VS_ON)));
  assert property (vsyncoff == (hreset && (vcount == VS_OFF)));
  assert property (vreset   == (hreset && (vcount == V_TOTAL-1)));

  // Combinational next-state nets
  assert property (next_hblank == (hreset ? 1'b0 : hblankon ? 1'b1 : hblank));
  assert property (next_vblank == (vreset ? 1'b0 : vblankon ? 1'b1 : vblank));

  // Counter updates
  assert property (past_valid && !$past(hreset) |-> hcount == $past(hcount) + 11'd1);
  assert property (past_valid &&  $past(hreset) |-> hcount == 11'd0);

  assert property (past_valid && !$past(hreset) |-> vcount == $past(vcount));
  assert property (past_valid &&  $past(hreset) && !$past(vreset) |-> vcount == $past(vcount) + 10'd1);
  assert property (past_valid &&  $past(hreset) &&  $past(vreset) |-> vcount == 10'd0);

  // hblank/vblank registered from next_*
  assert property (past_valid |-> hblank == $past(next_hblank));
  assert property (past_valid |-> vblank == $past(next_vblank));

  // Sync update rules (active-low, only change at their on/off events)
  assert property (past_valid |-> hsync == ($past(hsyncon) ? 1'b0 : $past(hsyncoff) ? 1'b1 : $past(hsync)));
  assert property (past_valid |-> vsync == ($past(vsyncon) ? 1'b0 : $past(vsyncoff) ? 1'b1 : $past(vsync)));
  assert property (past_valid && (hsync != $past(hsync)) |-> ($past(hsyncon) || $past(hsyncoff)));
  assert property (past_valid && (vsync != $past(vsync)) |-> ($past(vsyncon) || $past(vsyncoff)));

  // HSync correctness: high outside [839..966], exact low width 128
  assert property (past_valid && ($past(hcount) <= HS_ON-1) |-> hsync == 1'b1);
  assert property (past_valid && ($past(hcount) >= HS_OFF)  |-> hsync == 1'b1);
  assert property (past_valid &&  $past(hcount) == HS_ON    |-> (hsync == 1'b0)[*128] ##1 hsync == 1'b1);

  // VSync correctness: low from line 600..603, deassert at 604
  assert property (past_valid && $past(vsyncon) |-> (vsync == 1'b0) until_with $past(vsyncoff) ##1 vsync == 1'b1);

  // Blank output equals specified combinational function
  assert property (past_valid |-> blank == $past(next_vblank | (next_hblank & ~hreset)));

  // No horizontal blank on first pixel of a new line unless vertical blank starts
  assert property (past_valid && $past(hreset) && !$past(vblankon) |-> blank == 1'b0);

  // Interior active pixel must be unblanked (strictly inside visible area)
  assert property (past_valid && ($past(hcount) <= H_VISIBLE-2) && ($past(vcount) <= V_VISIBLE-2) |-> blank == 1'b0);

  // No X/Z after first cycle on key regs/outs
  assert property (past_valid |-> !$isunknown({hcount, vcount, hsync, vsync, blank, hblank, vblank}));

  // Coverage
  cover property (past_valid && $past(hsyncon) ##1 (hsync == 1'b0) ##[127] (hsync == 1'b0) ##1 (hsync == 1'b1));
  cover property (past_valid && $past(vsyncon) ##[1:$] $past(vsyncoff));
  cover property (past_valid && $past(hreset) && $past(vcount) == V_TOTAL-1); // frame end
  cover property (past_valid && $past(hcount) == H_VISIBLE-2 && $past(vcount) == V_VISIBLE-2 && blank == 1'b0);

endmodule

bind vga_controller vga_controller_sva sva (
  .vclock(vclock),
  .hcount(hcount),
  .vcount(vcount),
  .vsync(vsync),
  .hsync(hsync),
  .blank(blank),
  .hblank(hblank),
  .vblank(vblank),
  .hblankon(hblankon),
  .hsyncon(hsyncon),
  .hsyncoff(hsyncoff),
  .hreset(hreset),
  .vblankon(vblankon),
  .vsyncon(vsyncon),
  .vsyncoff(vsyncoff),
  .vreset(vreset),
  .next_hblank(next_hblank),
  .next_vblank(next_vblank)
);