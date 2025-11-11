// SVA checker for my_module. Bind this to the DUT.
module my_module_sva_bind
(
  input logic A1, A2, B1, B2, C1,
  input logic Y,
  input logic or0_out, or1_out, nand0_out_Y,
  input logic VPWR, VPB, VGND, VNB
);

  // Sample on any input edge; evaluate checks after combinational settle (##0)
  default clocking cb @(
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge B1 or negedge B1 or
    posedge B2 or negedge B2 or
    posedge C1 or negedge C1
  ); endclocking

  // Power rails must be correct
  assert property (1 |-> ##0 (VPWR==1 && VPB==1 && VGND==0 && VNB==0))
    else $error("Power rails incorrect");

  // No X/Z on key nets
  assert property (1 |-> ##0 !$isunknown({A1,A2,B1,B2,C1,Y,or0_out,or1_out,nand0_out_Y}))
    else $error("X/Z detected on inputs/outputs/internals");

  // Structural gate correctness
  assert property (1 |-> ##0 (or0_out == (B1 || B2)))
    else $error("or0_out != (B1|B2)");
  assert property (1 |-> ##0 (or1_out == (A1 || A2)))
    else $error("or1_out != (A1|A2)");
  assert property (1 |-> ##0 (nand0_out_Y == ~(or1_out && or0_out && C1)))
    else $error("nand0_out_Y incorrect");
  assert property (1 |-> ##0 (Y == nand0_out_Y))
    else $error("Y != nand0_out_Y");

  // End-to-end functional equivalence
  assert property (1 |-> ##0 (Y == ~((A1 || A2) && (B1 || B2) && C1)))
    else $error("Y functional mismatch");

  // Concise functional coverage
  // 1) Y forced high by C1=0
  cover property (1 |-> ##0 (!C1 && Y));

  // 2) Y high because A-group is 0 while others enable
  cover property (1 |-> ##0 (C1 && (B1||B2) && !(A1||A2) && Y));

  // 3) Y high because B-group is 0 while others enable
  cover property (1 |-> ##0 (C1 && (A1||A2) && !(B1||B2) && Y));

  // 4) Y low with A1 and B1 driving groups true
  cover property (1 |-> ##0 (C1 && A1 && !A2 && B1 && !B2 && !Y));

  // 5) Y low with A2 and B2 driving groups true
  cover property (1 |-> ##0 (C1 && !A1 && A2 && !B1 && B2 && !Y));

  // 6) Observe both output edges
  cover property (1 |-> ##0 $rose(Y));
  cover property (1 |-> ##0 $fell(Y));

endmodule

// Bind to the DUT (place in a package or a top-level TB file)
bind my_module my_module_sva_bind u_my_module_sva_bind (.*);