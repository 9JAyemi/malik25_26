// SVA checker for sky130_fd_sc_ms__clkdlyinv3sd3
module sky130_fd_sc_ms__clkdlyinv3sd3_sva (
  input logic A,
  input logic VPWR,
  input logic VGND,
  input logic VPB,
  input logic VNB,
  input logic clk,
  input logic Y
);
  logic pwr_good;
  assign pwr_good = (VPWR===1'b1) && (VGND===1'b0) && (VPB===VPWR) && (VNB===VGND);

  default clocking cb @(posedge clk); endclocking

  // Power pin sanity
  assert property (cb !$isunknown({VPWR,VGND}) |-> (VPWR===1'b1 && VGND===1'b0));
  assert property (cb !$isunknown({VPB,VNB,VPWR,VGND}) |-> (VPB===VPWR && VNB===VGND));

  // Functional inversion and X-propagation
  assert property (cb disable iff (!pwr_good) (!$isunknown(A) |-> (Y === ~A)));
  assert property (cb disable iff (!pwr_good) ( $isunknown(A) |->  $isunknown(Y)));

  // No clk sensitivity (combinational w.r.t. A)
  assert property (cb disable iff (!pwr_good) ($stable(A) |-> $stable(Y)));
  assert property (cb disable iff (!pwr_good) (!$stable(Y) |-> !$stable(A)));

  // Coverage
  cover  property (cb pwr_good && A==1'b0 && Y==1'b1);
  cover  property (cb pwr_good && A==1'b1 && Y==1'b0);
  cover  property (cb pwr_good && $rose(A) && $fell(Y));
  cover  property (cb pwr_good && $fell(A) && $rose(Y));
endmodule

bind sky130_fd_sc_ms__clkdlyinv3sd3 sky130_fd_sc_ms__clkdlyinv3sd3_sva sva_i (.*);