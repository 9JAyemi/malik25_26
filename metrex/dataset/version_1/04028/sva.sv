// SVA for vgabase. Bind this file to the DUT.
// Focus: counter sequencing, sync pulse timing/width, active-video window, and safety.

checker vgabase_sva
  #(parameter int unsigned hpixels = 12'd1344,
                         vlines  = 12'd806,
                         hsp     = 12'd136,
                         hbp     = 12'd160,
                         hfp     = 12'd24,
                         vsp     = 12'd6,
                         vbp     = 12'd29,
                         vfp     = 12'd3)
   (input logic               clk,
    input logic               clr,
    input logic               hsync,
    input logic               vsync,
    input logic [11:0]        hc,
    input logic [11:0]        vc,
    input logic               vidon);

  default clocking @(posedge clk); endclocking
  default disable iff (clr);

  // Static parameter sanity
  initial begin
    assert (hpixels > hsp + hbp + hfp) else $error("hpixels too small");
    assert (vlines  > vsp + vbp + vfp) else $error("vlines too small");
    assert (hsp > 0 && vsp > 0)        else $error("sync pulse must be > 0");
  end

  // No X on observable outputs/counters
  assert property (!$isunknown({hsync,vsync,vidon,hc,vc}));

  // Counter ranges
  assert property (hc < hpixels);
  assert property (vc < vlines);

  // Horizontal counter sequencing
  assert property ($past(hc) != hpixels-1 |=> hc == $past(hc) + 1);
  assert property ($past(hc) == hpixels-1 |=> hc == 12'd0);

  // Vertical counter sequencing on horizontal wrap
  assert property ($past(hc) != hpixels-1 |=> vc == $past(vc));
  assert property ($past(hc) == hpixels-1 && $past(vc) != vlines-1 |=> vc == $past(vc) + 1);
  assert property ($past(hc) == hpixels-1 && $past(vc) == vlines-1 |=> vc == 12'd0);

  // Syncs match their specified functions
  assert property (hsync == ~((hpixels - hsp - hbp < hc) && (hc <= hpixels - hbp)));
  assert property (vsync == ~((vlines  - vsp - vbp < vc) && (vc <= vlines  - vbp)));

  // Sync edges occur at expected counts
  localparam int unsigned H_FALL_CNT = hpixels - hsp - hbp + 1;
  localparam int unsigned H_RISE_CNT = hpixels - hbp + 1;
  localparam int unsigned V_FALL_CNT = vlines  - vsp  - vbp + 1;
  localparam int unsigned V_RISE_CNT = vlines  - vbp  + 1;

  assert property ($fell(hsync) |-> hc == H_FALL_CNT);
  assert property ($rose(hsync) |-> hc == H_RISE_CNT);
  assert property ($fell(vsync) |-> vc == V_FALL_CNT);
  assert property ($rose(vsync) |-> vc == V_RISE_CNT);

  // Exact pulse widths
  assert property ($fell(hsync) |-> !hsync[*hsp] ##1 hsync);
  assert property ($fell(vsync) |-> !vsync[*vsp] ##1 vsync);

  // Active video window
  assert property (vidon == ((hc < (hpixels - hfp - hsp - hbp)) &&
                             (vc < (vlines  - vfp  - vsp  - vbp))));

  // When video is active, syncs must be deasserted
  assert property (vidon |-> hsync && vsync);

  // Targeted coverage
  cover property ($past(hc)==hpixels-1 |=> hc==12'd0);      // end-of-line
  cover property ($fell(hsync));                             // hsync low observed
  cover property ($fell(vsync));                             // vsync low observed
  cover property (vidon && $rose(vidon));                    // entering active video
endchecker

bind vgabase vgabase_sva #(
  .hpixels(hpixels), .vlines(vlines),
  .hsp(hsp), .hbp(hbp), .hfp(hfp),
  .vsp(vsp), .vbp(vbp), .vfp(vfp)
) vgabase_sva_i (
  .clk(clk), .clr(clr), .hsync(hsync), .vsync(vsync),
  .hc(hc), .vc(vc), .vidon(vidon)
);