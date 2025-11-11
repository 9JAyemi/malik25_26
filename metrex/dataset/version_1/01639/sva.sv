// SVA for VGA1Interface
// Concise checks for counters, syncs, pixel gating, tile indexing, and basic coverage.

module VGA1Interface_sva (
  input  logic        clock,
  input  logic        reset,
  input  logic        clock2,
  input  logic [9:0]  CounterX,
  input  logic [8:0]  CounterY,
  input  logic        vga_hsync,
  input  logic        vga_vsync,
  input  logic        vga_r,
  input  logic        vga_g,
  input  logic        vga_b,
  input  logic        vga_HS,
  input  logic        vga_VS,
  input  logic        inDisplayArea,
  input  logic [2:0]  ix,
  input  logic [2:0]  iy,
  input  logic [63:0] framebuffer,
  input  logic        value
);
  default clocking cb2 @(posedge clock2); endclocking
  default disable iff (reset);

  // clock2 must toggle every posedge clock when not reset
  assert property (@(posedge clock) disable iff (reset) $changed(clock2))
    else $error("clock2 must toggle on every clock edge when not in reset");

  // CounterX legal range
  assert property (CounterX <= 10'd767)
    else $error("CounterX out of range");

  // CounterX next-state behavior
  assert property ($past(CounterX)!=10'd767 |=> CounterX == $past(CounterX)+10'd1)
    else $error("CounterX must increment by 1");
  assert property ($past(CounterX)==10'd767 |=> CounterX == 10'd0)
    else $error("CounterX must wrap to 0 at 767");

  // CounterY update only when X maxed, with wrap at 511
  assert property ($past(CounterX)!=10'd767 |=> CounterY == $past(CounterY))
    else $error("CounterY changed when CounterX not maxed");
  assert property ($past(CounterX)==10'd767 && $past(CounterY)!=9'd511 |=> CounterY == $past(CounterY)+9'd1)
    else $error("CounterY must increment by 1 on X wrap");
  assert property ($past(CounterX)==10'd767 && $past(CounterY)==9'd511 |=> CounterY == 9'd0)
    else $error("CounterY must wrap to 0 at 511");

  // Bounded liveness: see a CounterX max within 768 cycles
  assert property (1'b1 |-> ##[0:767] (CounterX==10'd767))
    else $error("Did not observe CounterX==767 within 768 cycles");

  // Sync outputs: active-low derived from counters
  assert property (vga_hsync == ~(CounterX[9:4]==6'd0))
    else $error("vga_hsync mismatch");
  assert property (vga_vsync == ~(CounterY==9'd0))
    else $error("vga_vsync mismatch");

  // RGB equality and gating
  assert property (vga_r == vga_g && vga_g == vga_b)
    else $error("RGB channels must be equal");
  assert property (vga_r == (value & inDisplayArea))
    else $error("RGB must equal value & inDisplayArea");
  assert property (!inDisplayArea |-> (!vga_r && !vga_g && !vga_b))
    else $error("RGB must be blank outside display area");

  // Tile index mapping for X (only when in display area)
  assert property (inDisplayArea && (CounterX < 10'd80)                    |-> ix==3'd0) else $error("ix mismatch");
  assert property (inDisplayArea && (CounterX >=10'd80  && CounterX <160) |-> ix==3'd1) else $error("ix mismatch");
  assert property (inDisplayArea && (CounterX >=10'd160 && CounterX <240) |-> ix==3'd2) else $error("ix mismatch");
  assert property (inDisplayArea && (CounterX >=10'd240 && CounterX <320) |-> ix==3'd3) else $error("ix mismatch");
  assert property (inDisplayArea && (CounterX >=10'd320 && CounterX <400) |-> ix==3'd4) else $error("ix mismatch");
  assert property (inDisplayArea && (CounterX >=10'd400 && CounterX <480) |-> ix==3'd5) else $error("ix mismatch");
  assert property (inDisplayArea && (CounterX >=10'd480 && CounterX <560) |-> ix==3'd6) else $error("ix mismatch");
  assert property (inDisplayArea && (CounterX >=10'd560 && CounterX <640) |-> ix==3'd7) else $error("ix mismatch");

  // Tile index mapping for Y (only when in display area)
  assert property (inDisplayArea && (CounterY <  9'd60)                    |-> iy==3'd0) else $error("iy mismatch");
  assert property (inDisplayArea && (CounterY >= 9'd60  && CounterY <120) |-> iy==3'd1) else $error("iy mismatch");
  assert property (inDisplayArea && (CounterY >= 9'd120 && CounterY <180) |-> iy==3'd2) else $error("iy mismatch");
  assert property (inDisplayArea && (CounterY >= 9'd180 && CounterY <240) |-> iy==3'd3) else $error("iy mismatch");
  assert property (inDisplayArea && (CounterY >= 9'd240 && CounterY <300) |-> iy==3'd4) else $error("iy mismatch");
  assert property (inDisplayArea && (CounterY >= 9'd300 && CounterY <360) |-> iy==3'd5) else $error("iy mismatch");
  assert property (inDisplayArea && (CounterY >= 9'd360 && CounterY <420) |-> iy==3'd6) else $error("iy mismatch");
  assert property (inDisplayArea && (CounterY >= 9'd420 && CounterY <480) |-> iy==3'd7) else $error("iy mismatch");

  // ix/iy stability when outside their update regions
  assert property ((CounterX>=10'd640 && $past(CounterX)>=10'd640) |-> ix==$past(ix))
    else $error("ix changed outside display area");
  assert property ((CounterY>= 9'd480 && $past(CounterY)>= 9'd480) |-> iy==$past(iy))
    else $error("iy changed outside display area");

  // Addressing: value equals framebuffer[{iy,ix}]
  assert property (value == framebuffer[{iy,ix}])
    else $error("value/framebuffer index mismatch");

  // No X/Z on key outputs
  assert property (!$isunknown({clock2, vga_hsync, vga_vsync, vga_r, vga_g, vga_b}))
    else $error("Unknown (X/Z) detected on outputs");

  // Coverage
  cover property ((CounterX==10'd0) ##[1:767] (CounterX==10'd767) ##1 (CounterX==10'd0));
  cover property (inDisplayArea && CounterX==10'd639 && CounterY==9'd479); // bottom-right active pixel
  cover property (vga_hsync==1'b0);
  cover property (vga_vsync==1'b0);
  cover property (!inDisplayArea && {vga_r,vga_g,vga_b}==3'b000);

  // Observe all tile indices 0..7 for ix and iy within display area
  generate
    genvar gi;
    for (gi=0; gi<8; gi++) begin : COV_TILES
      cover property (inDisplayArea && (ix == 3'(gi)));
      cover property (inDisplayArea && (iy == 3'(gi)));
    end
  endgenerate
endmodule

bind VGA1Interface VGA1Interface_sva sva (
  .clock(clock),
  .reset(reset),
  .clock2(clock2),
  .CounterX(CounterX),
  .CounterY(CounterY),
  .vga_hsync(vga_hsync),
  .vga_vsync(vga_vsync),
  .vga_r(vga_r),
  .vga_g(vga_g),
  .vga_b(vga_b),
  .vga_HS(vga_HS),
  .vga_VS(vga_VS),
  .inDisplayArea(inDisplayArea),
  .ix(ix),
  .iy(iy),
  .framebuffer(framebuffer),
  .value(value)
);