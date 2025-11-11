// SVA checker for sky130_fd_sc_lp__inputiso1n
module sky130_fd_sc_lp__inputiso1n_sva (
  input logic A,
  input logic SLEEP_B,
  input logic VPWR,
  input logic VGND,
  input logic VPB,
  input logic VNB,
  input logic X
);

  // Sample on any input edge
  default clocking cb @(
    posedge A or negedge A or
    posedge SLEEP_B or negedge SLEEP_B or
    posedge VPWR or negedge VPWR or
    posedge VGND or negedge VGND or
    posedge VPB  or negedge VPB  or
    posedge VNB  or negedge VNB
  ); endclocking

  // Functional equivalence (4-state aware)
  assert property (X === (!A && !SLEEP_B && !VPWR && !VGND && !VPB && !VNB))
    else $error("X != !A && !SLEEP_B && !VPWR && !VGND && !VPB && !VNB");

  // Output known when inputs are known
  assert property (!$isunknown({A,SLEEP_B,VPWR,VGND,VPB,VNB}) |-> !$isunknown(X))
    else $error("X is X/Z while all inputs are known");

  // Strong one-way implications (short-circuit guaranteed 0)
  assert property (A       === 1'b1 |-> X === 1'b0);
  assert property (SLEEP_B === 1'b1 |-> X === 1'b0);
  assert property (VPWR    === 1'b1 |-> X === 1'b0);
  assert property (VGND    === 1'b1 |-> X === 1'b0);
  assert property (VPB     === 1'b1 |-> X === 1'b0);
  assert property (VNB     === 1'b1 |-> X === 1'b0);

  // All zeros drive X high (4-state precise)
  assert property ((A===0 && SLEEP_B===0 && VPWR===0 && VGND===0 && VPB===0 && VNB===0) |-> X===1)
    else $error("All-zero inputs should produce X=1");

  // Minimal functional coverage
  cover property (!A && !SLEEP_B && !VPWR && !VGND && !VPB && !VNB && X); // X can be 1
  cover property ($rose(X));
  cover property ($fell(X));

endmodule

// Bind into the DUT
bind sky130_fd_sc_lp__inputiso1n sky130_fd_sc_lp__inputiso1n_sva sva_i (
  .A(A), .SLEEP_B(SLEEP_B), .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB), .X(X)
)