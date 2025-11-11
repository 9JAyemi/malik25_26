// SVA for sky130_fd_sc_hs__o311ai
// Function: Y = ~(C1 & B1 & (A1 | A2 | A3))

module sky130_fd_sc_hs__o311ai_sva;
  // In bound scope: A1,A2,A3,B1,C1,VPWR,VGND,Y,B1_or0_out,nand0_out_Y must exist
  wire or_out = (A1 | A2 | A3);

  default clocking cb @(*); endclocking
  // Only check when power-good; ignore otherwise
  default disable iff (!(VPWR===1'b1 && VGND===1'b0));

  // Functional equivalence (end-to-end)
  assert property (Y === ~(C1 & B1 & or_out));

  // Structural sub-checks
  assert property (B1_or0_out === or_out);
  assert property (nand0_out_Y === ~(C1 & B1_or0_out & B1));
  assert property (Y === nand0_out_Y);

  // No X on Y when inputs are known
  assert property (!$isunknown({A1,A2,A3,B1,C1}) |-> !$isunknown(Y));

  // Corner truth checks
  assert property ((B1===1'b0 || C1===1'b0) && !$isunknown({A1,A2,A3,B1,C1}) |-> Y===1'b1);
  assert property (B1===1'b1 && C1===1'b1 && (A1||A2||A3) && !$isunknown({A1,A2,A3,B1,C1}) |-> Y===1'b0);
  assert property (B1===1'b1 && C1===1'b1 && !(A1||A2||A3) && !$isunknown({A1,A2,A3,B1,C1}) |-> Y===1'b1);

  // Basic coverage: both output values under power-good
  cover property (Y===1'b0);
  cover property (Y===1'b1);

  // Input influence coverage: each input can drive Y low when enabled
  cover property (!A1 && !A2 && !A3 && B1 && C1 ##1 A1 && $stable({A2,A3,B1,C1}) && Y===1'b0);
  cover property ((A1||A2||A3) && !B1 && C1 ##1 B1 && $stable({A1,A2,A3,C1}) && Y===1'b0);
  cover property ((A1||A2||A3) && B1 && !C1 ##1 C1 && $stable({A1,A2,A3,B1}) && Y===1'b0);

  // Complementary rises of Y when disabling any input
  cover property (A1 && !A2 && !A3 && B1 && C1 ##1 !A1 && $stable({A2,A3,B1,C1}) && Y===1'b1);
  cover property ((A1||A2||A3) && B1 && C1 ##1 !B1 && $stable({A1,A2,A3,C1}) && Y===1'b1);
  cover property ((A1||A2||A3) && B1 && C1 ##1 !C1 && $stable({A1,A2,A3,B1}) && Y===1'b1);
endmodule

bind sky130_fd_sc_hs__o311ai sky130_fd_sc_hs__o311ai_sva o311ai_sva_i();