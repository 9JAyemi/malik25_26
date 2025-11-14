// SVA for the provided design. Bind these in your simulation.

`ifndef VGA_SVA
`define VGA_SVA

// counterModulo assertions
module counterModulo_sva #(parameter int n=10, safe=1)
(
  input logic                clk,
  input logic [n-1:0]        modulo,
  input logic [n-1:0]        count,
  input logic                oClk
);
  default clocking cb @(posedge clk); endclocking
  default disable iff ($isunknown({clk,modulo,count}));

  // Safety/range and X-free oClk
  assert property ( safe || (count < modulo) );
  assert property ( !$isunknown(oClk) );

  // Next-state behavior
  assert property ( !oClk |=> count == $past(count)+1 );
  assert property (  oClk |=> count == '0 );

  // oClk meaning (when in-range)
  assert property ( (count < modulo) |-> (oClk == (count+1 == modulo)) );

  // One-cycle pulse when modulo>1
  assert property ( (count < modulo && modulo > 1) |-> (oClk |=> !oClk) );

  // Covers
  cover property ( (modulo>1) ##1 (count==modulo-1 && oClk) ##1 (count==0 && !oClk) );
  cover property ( (modulo==1) ##1 oClk );
endmodule

bind counterModulo counterModulo_sva #(.n(n), .safe(safe)) u_counterModulo_sva
(
  .clk   (clk),
  .modulo(modulo),
  .count (count),
  .oClk  (oClk)
);

// vgaRotatingCounter assertions
module vgaRotatingCounter_sva
#(parameter int ta=96, tb=16, tc=640, td=48)
(
  input logic        clk,
  input logic [1:0]  stage,
  input logic [9:0]  count,
  input logic        outClk,
  input logic        stageClk,
  input logic [9:0]  modulo
);
  localparam int A=0, B=1, C=2, D=3;

  default clocking cb @(posedge clk); endclocking
  default disable iff ($isunknown({clk,stage,count,outClk,stageClk,modulo}));

  // Stage range and sequencing
  assert property ( stage inside {[A:D]} );
  assert property ( !stageClk |=> stage == $past(stage) );
  assert property (  stageClk |=> stage == $past(stage)+2'd1 );

  // Modulo mapping and stageClk meaning
  assert property ( modulo == (stage==A ? ta : stage==B ? tb : stage==C ? tc : td) );
  assert property ( (count < modulo) |-> (stageClk == (count+1 == modulo)) );

  // outClk is single-cycle pulse at end of stage D (given ta/tb/tc/td > 1)
  assert property ( outClk |-> ($past(stage)==D && $past(stageClk)) );
  assert property ( (ta>1 && tb>1 && tc>1 && td>1) |-> (outClk |=> !outClk) );

  // Cover a full rotation and terminal pulse
  cover property ( stage==A && count==0 ##1 stage==B ##1 stage==C ##1 stage==D ##1 outClk );
endmodule

bind vgaRotatingCounter vgaRotatingCounter_sva #(.ta(ta), .tb(tb), .tc(tc), .td(td)) u_vgaRotatingCounter_sva
(
  .clk     (clk),
  .stage   (stage),
  .count   (count),
  .outClk  (outClk),
  .stageClk(stageClk),
  .modulo  (modulo)
);

// vgaControl assertions
module vgaControl_sva
#(parameter int ha=120, hb=64, hc=800, hd=56)
(
  input logic       clk,
  input logic       VGA_VS, VGA_HS,
  input logic       need,
  input logic [9:0] hNeed, vNeed,
  input logic [1:0] hStage, vStage,
  input logic [9:0] hCount, vCount,
  input logic       vClock, vEnd
);
  localparam int A=0, B=1, C=2, D=3;

  default clocking cb @(posedge clk); endclocking
  default disable iff ($isunknown({clk,VGA_VS,VGA_HS,need,hNeed,vNeed,hStage,vStage,hCount,vCount,vClock,vEnd}));

  // Registered HS/VS from previous stage values
  assert property ( VGA_HS == $past(hStage!=A) );
  assert property ( VGA_VS == $past(vStage!=A) );

  // Combinational outputs
  assert property ( need  == (vStage==C && ((hStage==C && hCount!=hc-1) || (hStage==B && hCount==hb-1))) );
  assert property ( hNeed == (hStage==C ? hCount+1 : 10'd0) );
  assert property ( vNeed == vCount );

  // vClock handshake with horizontal end (D->A) and one-cycle pulse
  assert property ( vClock |=> ($past(hStage)==D && hStage==A && hCount==0) );
  assert property ( vClock |=> !vClock );

  // vEnd is a one-cycle pulse
  assert property ( vEnd |=> !vEnd );

  // Covers of key events
  cover property ( vClock ##1 vEnd );
  cover property ( vStage==C && hStage==B && hCount==hb-1 && need );
  cover property ( vStage==C && hStage==C && hCount!=hc-1 && need );
endmodule

bind vgaControl vgaControl_sva #(.ha(ha), .hb(hb), .hc(hc), .hd(hd)) u_vgaControl_sva
(
  .clk    (clk),
  .VGA_VS (VGA_VS),
  .VGA_HS (VGA_HS),
  .need   (need),
  .hNeed  (hNeed),
  .vNeed  (vNeed),
  .hStage (hStage),
  .vStage (vStage),
  .hCount (hCount),
  .vCount (vCount),
  .vClock (vClock),
  .vEnd   (vEnd)
);

`endif