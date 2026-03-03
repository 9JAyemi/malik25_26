// SVA checker for module voltage_supply
// Concise, high-quality checks and coverage

module voltage_supply_sva (
  input logic clk,
  input logic rst,
  input logic enable,
  input logic VPWR,
  input logic VGND,
  input logic VPB,
  input logic VNB
);

  default clocking cb @ (posedge clk); endclocking

  // Rails are constant and never X/Z
  assert property (@cb !$isunknown({VPWR,VGND}) && VPWR==1'b1 && VGND==1'b0);
  assert property (@cb $stable(VPWR) && $stable(VGND));

  // VNB is always 0 and never X/Z
  assert property (@cb !$isunknown(VNB) && VNB==1'b0);

  // Asynchronous reset clears outputs immediately
  assert property (@(posedge rst) (VPB==1'b0 && VNB==1'b0));

  // While reset is held, outputs remain cleared
  assert property (@cb rst |-> (VPB==1'b0 && VNB==1'b0));

  // When enable is 0 at a clock edge (and not in reset), outputs go 0 immediately (same tick after NBA)
  assert property (@cb !rst && !enable |-> ##0 (VPB==1'b0 && VNB==1'b0));

  // When enable is 0 at a clock edge (and not in reset), outputs are 0 next cycle as well
  assert property (@cb disable iff (rst) !enable |=> (VPB==1'b0 && VNB==1'b0));

  // When enable is 1 at a clock edge (and not in reset), VPB toggles by the next clock
  // (Assumes clock period exceeds the #2 delay in the DUT)
  assert property (@cb disable iff (rst) enable |=> VPB == ~$past(VPB));

  // Outputs never go X/Z
  assert property (@cb !$isunknown({VPWR,VGND,VPB,VNB}));

  // ----------------
  // Functional coverage
  // ----------------

  // Cover async reset taking effect
  cover property (@(posedge rst) VPB==1'b0 && VNB==1'b0);

  // Cover a disable forcing zeros immediately
  cover property (@cb !rst && !enable ##0 (VPB==1'b0 && VNB==1'b0));

  // Cover at least one toggle due to enable
  cover property (@cb disable iff (rst) enable ##1 (VPB == ~$past(VPB)));

  // Cover sustained enable causing two successive toggles
  cover property (@cb disable iff (rst)
                  enable ##1 (VPB == ~$past(VPB))
                  ##1 enable ##1 (VPB == ~$past(VPB)));

  // Cover rails holding constant for 3 cycles
  cover property (@cb (VPWR==1'b1 && VGND==1'b0)[*3]);

endmodule

// Bind into the DUT
bind voltage_supply voltage_supply_sva sva_i (
  .clk(clk),
  .rst(rst),
  .enable(enable),
  .VPWR(VPWR),
  .VGND(VGND),
  .VPB(VPB),
  .VNB(VNB)
);