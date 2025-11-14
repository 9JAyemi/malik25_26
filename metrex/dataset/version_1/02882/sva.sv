// SVA for module camera
module camera_sva;

  // constants from RTL
  localparam int HS_MAX = 13'd1567;
  localparam int HS_ACTIVE_MAX = 13'd1280;
  localparam int VS_MAX = 10'd510;

  default clocking cb @(negedge refclk); endclocking

  // pixclk must mirror refclk
  assert property (@(posedge refclk or negedge refclk) pixclk == refclk)
    else $error("pixclk must equal refclk");

  // clk2 must toggle every negedge refclk
  assert property (!$isunknown($past(clk2)) |-> clk2 != $past(clk2))
    else $error("clk2 did not toggle on negedge refclk");

  // Reset behavior
  assert property (!reset_n |-> hs_counter==0 && vs_counter==0 && data==8'h00 && !vsync && !hsync)
    else $error("Reset behavior violated");

  // Counter ranges
  assert property (reset_n |-> hs_counter <= HS_MAX) else $error("hs_counter out of range");
  assert property (reset_n |-> vs_counter <= VS_MAX) else $error("vs_counter out of range");

  // hs_counter step and wrap
  assert property (reset_n && $past(reset_n) && $past(hs_counter)!=HS_MAX |-> hs_counter==$past(hs_counter)+1)
    else $error("hs_counter did not increment");
  assert property (reset_n && $past(reset_n) && $past(hs_counter)==HS_MAX |-> hs_counter==0)
    else $error("hs_counter did not wrap to 0");

  // vs_counter step on hs wrap, else hold
  assert property (reset_n && $past(reset_n) && $past(hs_counter)==HS_MAX |-> 
                   vs_counter==($past(vs_counter)==VS_MAX ? 10'd0 : $past(vs_counter)+1))
    else $error("vs_counter step/wrap wrong on hs wrap");
  assert property (reset_n && $past(reset_n) && $past(hs_counter)!=HS_MAX |-> vs_counter==$past(vs_counter))
    else $error("vs_counter changed without hs wrap");

  // Exact equations for syncs
  assert property (vsync == (reset_n && (vs_counter < 10'd3)))
    else $error("vsync equation mismatch");
  assert property (hsync == (reset_n && (vs_counter > 10'd19) && (vs_counter < 10'd500) && (hs_counter < HS_ACTIVE_MAX)))
    else $error("hsync equation mismatch");
  assert property (vsync |-> !hsync) else $error("vsync and hsync overlap");

  // Data formatting (byte selection by clk2 level)
  assert property (reset_n && !clk2 |-> data == pixel_counter[15:8])
    else $error("Upper byte mapping to data wrong");
  assert property (reset_n &&  clk2 |-> data == pixel_counter[7:0])
    else $error("Lower byte mapping to data wrong");

  // pixel_counter behavior on clk2 domain
  assert property (@(posedge clk2) (hs_counter==13'd1566) |-> (pixel_counter==17'd0))
    else $error("pixel_counter did not reset at hs_counter==1566");
  assert property (@(posedge clk2) (hs_counter!=13'd1566) |-> (pixel_counter==$past(pixel_counter)+1))
    else $error("pixel_counter did not increment on clk2 posedge");

  // Coverage
  cover property (reset_n ##1 hs_counter==HS_MAX ##1 hs_counter==0);                            // line wrap
  cover property (reset_n && hs_counter==HS_MAX && vs_counter==VS_MAX ##1 vs_counter==0);      // frame wrap
  cover property (reset_n && vs_counter==10'd0 && vsync);                                      // vsync asserted
  cover property (reset_n && vs_counter==10'd20 && hs_counter==13'd0 && hsync);                // hsync start in active video
  cover property (reset_n && vs_counter==10'd20 && hs_counter==13'd1280 && !hsync);            // hsync end in active video
  cover property (reset_n && !clk2 ##0 data==pixel_counter[15:8]);                              // upper byte driven
  cover property (reset_n &&  clk2 ##0 data==pixel_counter[7:0]);                               // lower byte driven

endmodule

bind camera camera_sva camera_sva_i();