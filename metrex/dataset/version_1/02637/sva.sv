// SVA for sky130_fd_sc_hs__nand4
// Bind into the DUT to check power, function, structure, and basic coverage.
module sky130_fd_sc_hs__nand4_sva (
  input A, B, C, D,
  input VPWR, VGND,
  input Y,
  input nand1, nand2, nand3
);
  // Enable assertions only when rails are good
  wire pgood = (VPWR===1'b1) && (VGND===1'b0);
  default disable iff (!pgood)
  default clocking cb @(A or B or C or D or VPWR or VGND or Y); endclocking

  // Environment: rails must be valid
  assume property (VPWR===1'b1 && VGND===1'b0);

  // Golden functional spec: true 4-input NAND
  assert property (Y === ~(A & B & C & D));

  // Structural checks on internal nodes
  assert property (nand1 === ~(A & B));
  assert property (nand2 === ~(C & D));
  assert property (nand3 === ~(nand1 & nand2));
  assert property (Y === nand3);

  // Derived algebraic equivalence of current structure
  assert property (Y === ((A & B) | (C & D)));

  // Known-ness: known inputs imply known output
  assert property (!$isunknown({A,B,C,D})) |-> !$isunknown(Y);

  // No spontaneous output activity
  assert property (@(posedge Y or negedge Y) $changed({A,B,C,D}));

  // Coverage
  cover property (Y==1);
  cover property (Y==0);
  cover property (A & B);
  cover property (C & D);
  cover property (A & B & C & D);
endmodule

bind sky130_fd_sc_hs__nand4 sky130_fd_sc_hs__nand4_sva u_nand4_sva (.*);