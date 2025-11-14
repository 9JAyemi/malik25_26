// SVA for vga640x480
// Bind into the DUT to access internals (HCS, VCS, VSenable, and params)

module vga640x480_sva
  #(parameter int hpixels = 800,
              int vlines  = 521,
              int hbp     = 144,
              int hfp     = 784,
              int vbp     = 31,
              int vfp     = 511)
(
  input  logic        CLK,
  input  logic        CLR,
  input  logic        HSYNC,
  input  logic        VSYNC,
  input  logic        VIDON,
  input  logic [9:0]  HCS,
  input  logic [9:0]  VCS,
  input  logic        VSenable
);

default clocking cb @(posedge CLK); endclocking

// Constant sanity
initial begin
  assert (hbp < hfp && vbp < vfp);
  assert (hpixels > hfp && vlines > vfp);
end

// Synchronous reset behavior
assert property (@(posedge CLK) CLR |-> (HCS==10'd0 && VCS==10'd0));

// Range and no-X
assert property (@(posedge CLK) HCS < hpixels && VCS < vlines);
assert property (@(posedge CLK) !$isunknown({HCS,VCS,HSYNC,VSYNC,VIDON,VSenable}));

// H counter: increment and wrap, and VSenable pulse generation
assert property (@(posedge CLK) disable iff (CLR)
  (HCS < hpixels-1) |=> (HCS == $past(HCS)+1 && VSenable==1'b0));
assert property (@(posedge CLK) disable iff (CLR)
  (HCS == hpixels-1) |=> (HCS == 10'd0 && VSenable==1'b1));
assert property (@(posedge CLK) disable iff (CLR)
  VSenable |-> ($past(HCS) == hpixels-1 && HCS == 10'd0));
assert property (@(posedge CLK) disable iff (CLR)
  VSenable |=> !VSenable);

// V counter: hold, increment on line end, wrap at frame end
assert property (@(posedge CLK) disable iff (CLR)
  !VSenable |=> VCS == $past(VCS));
assert property (@(posedge CLK) disable iff (CLR)
  (VSenable && VCS < vlines-1) |=> VCS == $past(VCS)+1);
assert property (@(posedge CLK) disable iff (CLR)
  (VSenable && VCS == vlines-1) |=> VCS == 10'd0);

// HSYNC/VSYNC functional mapping and edge locations
assert property (@(posedge CLK) disable iff (CLR) (HCS < 10'd128) |-> !HSYNC);
assert property (@(posedge CLK) disable iff (CLR) (HCS >= 10'd128) |-> HSYNC);
assert property (@(posedge CLK) disable iff (CLR) (VCS < 10'd2)   |-> !VSYNC);
assert property (@(posedge CLK) disable iff (CLR) (VCS >= 10'd2)  |-> VSYNC);

assert property (@(posedge CLK) disable iff (CLR)
  $rose(HSYNC) |-> ($past(HCS)==10'd127 && HCS==10'd128));
assert property (@(posedge CLK) disable iff (CLR)
  $fell(HSYNC) |-> ($past(HCS)==hpixels-1 && HCS==10'd0));

assert property (@(posedge CLK) disable iff (CLR)
  $rose(VSYNC) |-> ($past(VCS)==10'd1 && VCS==10'd2 && HCS==10'd0));
assert property (@(posedge CLK) disable iff (CLR)
  $fell(VSYNC) |-> ($past(VCS)==vlines-1 && VCS==10'd0 && HCS==10'd0));

// Optional exact pulse widths (low) for syncs
assert property (@(posedge CLK) disable iff (CLR)
  $fell(HSYNC) |-> (!HSYNC[*127]) ##1 $rose(HSYNC));
assert property (@(posedge CLK) disable iff (CLR)
  $fell(VSYNC) |-> (!VSYNC[*((hpixels*2)-1)]) ##1 $rose(VSYNC));

// Active video window (VIDON)
assert property (@(posedge CLK) disable iff (CLR)
  VIDON == ((HCS >= hbp && HCS < hfp) && (VCS >= vbp && VCS < vfp)));

// VIDON edge locations (either horizontal or vertical boundary)
assert property (@(posedge CLK) disable iff (CLR)
  $rose(VIDON) |-> ((HCS==hbp && VCS>=vbp && VCS<vfp) ||
                    (VCS==vbp && HCS>=hbp && HCS<hfp)));
assert property (@(posedge CLK) disable iff (CLR)
  $fell(VIDON) |-> ((HCS==hfp && VCS>=vbp && VCS<vfp) ||
                    (VCS==vfp && HCS>=hbp && HCS<hfp)));

// Coverage
cover property (@(posedge CLK) disable iff (CLR) $fell(HSYNC));       // line start
cover property (@(posedge CLK) disable iff (CLR) VSenable);           // line wrap pulse
cover property (@(posedge CLK) disable iff (CLR) $fell(VSYNC));       // frame start
cover property (@(posedge CLK) disable iff (CLR) $rose(VSYNC));       // end of vsync pulse
cover property (@(posedge CLK) disable iff (CLR) (HCS==hbp   && VCS==vbp   && VIDON)); // top-left active
cover property (@(posedge CLK) disable iff (CLR) (HCS==hfp-1 && VCS==vbp   && VIDON)); // top-right active
cover property (@(posedge CLK) disable iff (CLR) (HCS==hbp   && VCS==vfp-1 && VIDON)); // bottom-left active
cover property (@(posedge CLK) disable iff (CLR) (HCS==hfp-1 && VCS==vfp-1 && VIDON)); // bottom-right active

endmodule

bind vga640x480 vga640x480_sva
  #(.hpixels(hpixels), .vlines(vlines), .hbp(hbp), .hfp(hfp), .vbp(vbp), .vfp(vfp))
  vga640x480_sva_i ( .CLK(CLK), .CLR(CLR),
                     .HSYNC(HSYNC), .VSYNC(VSYNC), .VIDON(VIDON),
                     .HCS(HCS), .VCS(VCS), .VSenable(VSenable) );