// SVA checker for sky130_fd_sc_hd__nor2
module sky130_fd_sc_hd__nor2_sva (
  input logic A,
  input logic B,
  input logic Y,
  input logic VPWR,
  input logic VGND,
  input logic VPB,
  input logic VNB,
  input logic nor0_out_Y
);

  // Sample on any relevant edge
  default clocking cb @(posedge A or negedge A or posedge B or negedge B or posedge Y or negedge Y); endclocking

  // Power pins must be correct and constant
  initial begin
    assert (VPWR === 1'b1 && VGND === 1'b0 && VPB === 1'b1 && VNB === 1'b0)
      else $error("Power pins not at expected constants");
  end
  assert property (VPWR === 1'b1 && VGND === 1'b0 && VPB === 1'b1 && VNB === 1'b0);

  // Functional correctness (truth table) when inputs are known
  assert property (!$isunknown({A,B}) |-> (Y === ~(A | B)));

  // Strong implications that hold even with X on the other input
  assert property ((A === 1'b1 || B === 1'b1) |-> (Y === 1'b0));
  assert property ((A === 1'b0 && B === 1'b0) |-> (Y === 1'b1));

  // Internal buffer consistency
  assert property (Y === nor0_out_Y);
  assert property (!$isunknown({A,B}) |-> (nor0_out_Y === ~(A | B)));

  // No spurious output changes; pure combinational behavior
  assert property ($changed(Y) |-> ($changed(A) || $changed(B)));
  assert property ($stable({A,B}) |-> $stable(Y));

  // Output must be known when inputs are known
  assert property (!$isunknown({A,B}) |-> !$isunknown(Y));

  // Basic functional coverage
  cover property (A===1'b0 && B===1'b0 && Y===1'b1);
  cover property (A===1'b1 && B===1'b0 && Y===1'b0);
  cover property (A===1'b0 && B===1'b1 && Y===1'b0);
  cover property (A===1'b1 && B===1'b1 && Y===1'b0);

  // Edge coverage
  cover property ($rose(Y));
  cover property ($fell(Y));
  cover property ((A===1'b0 && B===1'b0) ##1 (A===1'b1 && Y===1'b0));
  cover property ((A===1'b0 && B===1'b0) ##1 (B===1'b1 && Y===1'b0));
  cover property ((A===1'b1 && B===1'b1) ##1 (A===1'b0 && B===1'b0 && Y===1'b1));

endmodule

// Bind the checker to all instances of the DUT (connects internal nor0_out_Y via .*)
bind sky130_fd_sc_hd__nor2 sky130_fd_sc_hd__nor2_sva dut_sva (.*);