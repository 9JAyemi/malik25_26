// SVA checker for VgaTiming
module VgaTiming_sva #(
  parameter int H_TOTAL_TIME = 800,
  parameter int H_BLNK_START = 640,
  parameter int H_SYNC_START = 656,
  parameter int H_SYNC_TIME  = 96,
  parameter int H_SYNC_POL   = 0,
  parameter int V_TOTAL_TIME = 525,
  parameter int V_BLNK_START = 480,
  parameter int V_SYNC_START = 490,
  parameter int V_SYNC_TIME  = 2,
  parameter int V_SYNC_POL   = 0
)(
  input  logic        pclk,
  input  logic        rst,
  input  logic [9:0]  hcount,
  input  logic        hsync,
  input  logic [9:0]  vcount,
  input  logic        vsync,
  input  logic        blnk,
  input  logic        hblnk,   // internal
  input  logic        vblnk    // internal
);

  localparam bit HS_ACT = (H_SYNC_POL != 0);
  localparam bit VS_ACT = (V_SYNC_POL != 0);

  default clocking cb @(posedge pclk); endclocking
  default disable iff (rst);

  // Reset state
  assert property (@(posedge pclk) rst |-> (hcount==0 && vcount==0 && hsync==0 && vsync==0 && hblnk==0 && vblnk==0));

  // No Xs when not in reset
  assert property (!$isunknown({hcount,vcount,hsync,vsync,blnk}));

  // Range checks
  assert property (hcount < H_TOTAL_TIME);
  assert property (vcount < V_TOTAL_TIME);

  // hcount step/wrap
  assert property (($past(hcount) != H_TOTAL_TIME-1) |-> hcount == $past(hcount)+1);
  assert property (($past(hcount) == H_TOTAL_TIME-1) |-> hcount == 0);

  // vcount step/wrap (only when hcount wraps)
  assert property (($past(hcount) == H_TOTAL_TIME-1 && $past(vcount) != V_TOTAL_TIME-1) |-> vcount == $past(vcount)+1);
  assert property (($past(hcount) == H_TOTAL_TIME-1 && $past(vcount) == V_TOTAL_TIME-1) |-> vcount == 0);
  assert property (($past(hcount) != H_TOTAL_TIME-1) |-> vcount == $past(vcount));

  // hsync level by horizontal position
  assert property ((hcount >= H_SYNC_START && hcount < H_SYNC_START+H_SYNC_TIME) |-> hsync == HS_ACT);
  assert property (!(hcount >= H_SYNC_START && hcount < H_SYNC_START+H_SYNC_TIME) |-> hsync == ~HS_ACT);

  // hblnk level by horizontal position
  assert property ((hcount >= H_BLNK_START) |-> hblnk);
  assert property ((hcount <  H_BLNK_START) |-> !hblnk);

  // vsync level by vertical position
  assert property ((vcount >= V_SYNC_START && vcount < V_SYNC_START+V_SYNC_TIME) |-> vsync == VS_ACT);
  assert property (!(vcount >= V_SYNC_START && vcount < V_SYNC_START+V_SYNC_TIME) |-> vsync == ~VS_ACT);

  // vblnk level by vertical position
  assert property ((vcount >= V_BLNK_START) |-> vblnk);
  assert property ((vcount <  V_BLNK_START) |-> !vblnk);

  // blnk is exact combinational function of hblnk/vblnk
  assert property (blnk == ~(hblnk | vblnk));

  // Legal change points (edges only where designed)
  assert property ((hsync != $past(hsync)) |->
                   ($past(hcount) == H_BLNK_START-1 ||
                    $past(hcount) == H_SYNC_START-1 ||
                    $past(hcount) == H_SYNC_START+H_SYNC_TIME-1 ||
                    $past(hcount) == H_TOTAL_TIME-1));

  assert property ((hblnk != $past(hblnk)) |->
                   ($past(hcount) == H_BLNK_START-1 ||
                    $past(hcount) == H_TOTAL_TIME-1));

  assert property ((vsync != $past(vsync)) |->
                   ($past(hcount) == H_TOTAL_TIME-1 &&
                   ($past(vcount) == V_BLNK_START-1 ||
                    $past(vcount) == V_SYNC_START-1 ||
                    $past(vcount) == V_SYNC_START+V_SYNC_TIME-1 ||
                    $past(vcount) == V_TOTAL_TIME-1)));

  assert property ((vblnk != $past(vblnk)) |->
                   ($past(hcount) == H_TOTAL_TIME-1 &&
                   ($past(vcount) == V_BLNK_START-1 ||
                    $past(vcount) == V_TOTAL_TIME-1)));

  // Pulse-width checks
  assert property ( (hcount == H_SYNC_START) |-> (hsync == HS_ACT)[*H_SYNC_TIME] ##1 (hsync == ~HS_ACT) );

  // Vsync pulse width checked at line starts only
  assert property (@(posedge pclk iff (!rst && hcount==0))
                   (vcount == V_SYNC_START) |-> (vsync == VS_ACT)[*V_SYNC_TIME] ##1 (vsync == ~VS_ACT));

  // Coverage
  cover property (hcount == 0 ##[1:H_TOTAL_TIME] hcount == 0);                              // one full line
  cover property (@(posedge pclk iff (!rst && hcount==0)) vcount == 0 ##[1:V_TOTAL_TIME] vcount == 0); // one full frame
  cover property (hcount == H_SYNC_START && hsync == HS_ACT ##[H_SYNC_TIME] hcount == H_SYNC_START+H_SYNC_TIME && hsync == ~HS_ACT);
  cover property (@(posedge pclk iff (!rst && hcount==0)) vcount == V_SYNC_START && vsync == VS_ACT
                  ##[V_SYNC_TIME] vcount == V_SYNC_START+V_SYNC_TIME && vsync == ~VS_ACT);
  cover property (hcount == H_BLNK_START && hblnk);
  cover property (@(posedge pclk iff (!rst && hcount==0)) vcount == V_BLNK_START && vblnk);

endmodule

// Bind into DUT
bind VgaTiming VgaTiming_sva #(
  .H_TOTAL_TIME(H_TOTAL_TIME),
  .H_BLNK_START(H_BLNK_START),
  .H_SYNC_START(H_SYNC_START),
  .H_SYNC_TIME (H_SYNC_TIME),
  .H_SYNC_POL  (H_SYNC_POL),
  .V_TOTAL_TIME(V_TOTAL_TIME),
  .V_BLNK_START(V_BLNK_START),
  .V_SYNC_START(V_SYNC_START),
  .V_SYNC_TIME (V_SYNC_TIME),
  .V_SYNC_POL  (V_SYNC_POL)
) VgaTiming_sva_i (
  .pclk  (pclk),
  .rst   (rst),
  .hcount(hcount),
  .hsync (hsync),
  .vcount(vcount),
  .vsync (vsync),
  .blnk  (blnk),
  .hblnk (hblnk),
  .vblnk (vblnk)
);