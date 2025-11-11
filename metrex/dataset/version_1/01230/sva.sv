// SVA checker for logic_module
module logic_module_sva (
  input logic A1, A2, A3, B1, B2,
  input logic Y,
  input logic nand0_out, nand1_out, and0_out_Y,
  input logic VPWR, VGND, VPB, VNB
);

  default clocking cb @ (posedge $global_clock); endclocking

  // Power rails must be correct constants
  assert property (1'b1 |-> ##0 (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0))
    else $error("Power rails incorrect");

  // Gate-local equivalence checks (guarded against X on inputs)
  assert property ((!$isunknown({A1,A2,A3})) |-> ##0 (nand0_out == ~(A1 & A2 & A3)))
    else $error("nand0_out mismatch");
  assert property ((!$isunknown({B1,B2})) |-> ##0 (nand1_out == ~(B1 & B2)))
    else $error("nand1_out mismatch");
  assert property ((!$isunknown({nand0_out,nand1_out})) |-> ##0 (and0_out_Y == (nand0_out & nand1_out)))
    else $error("and0_out_Y mismatch");
  assert property ((!$isunknown(and0_out_Y)) |-> ##0 (Y == and0_out_Y))
    else $error("buf0/Y mismatch");

  // Top-level functional equivalence
  assert property ((!$isunknown({A1,A2,A3,B1,B2})) |-> ##0
                   (Y == ~((A1 & A2 & A3) | (B1 & B2))))
    else $error("Y functional mismatch");

  // No X on Y when inputs are known
  assert property ((!$isunknown({A1,A2,A3,B1,B2})) |-> ##0 !$isunknown(Y))
    else $error("Y is X/Z with known inputs");

  // Output reaction to enabling terms rising
  assert property ($rose(A1 & A2 & A3) |-> ##0 (Y==1'b0))
    else $error("Y failed to go low when A1&A2&A3 rose");
  assert property ($rose(B1 & B2) |-> ##0 (Y==1'b0))
    else $error("Y failed to go low when B1&B2 rose");

  // Coverage: output toggles
  cover property ($rose(Y));
  cover property ($fell(Y));

  // Coverage: all four term quadrants
  cover property ((~(A1 & A2 & A3)) && (~(B1 & B2)) && (Y==1'b1));
  cover property (( (A1 & A2 & A3)) && (~(B1 & B2)) && (Y==1'b0));
  cover property ((~(A1 & A2 & A3)) && ( (B1 & B2)) && (Y==1'b0));
  cover property (( (A1 & A2 & A3)) && ( (B1 & B2)) && (Y==1'b0));

endmodule

// Bind into the DUT
bind logic_module logic_module_sva u_logic_module_sva (
  .A1(A1), .A2(A2), .A3(A3), .B1(B1), .B2(B2),
  .Y(Y),
  .nand0_out(nand0_out), .nand1_out(nand1_out), .and0_out_Y(and0_out_Y),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);