// SVA checker for my_module
module my_module_sva (
  input logic Y, A1, A2, B1, B2,
  input logic VPWR, VGND, VPB, VNB,
  // internal nets
  input logic nand0_out, nand1_out, and0_out_Y
);
  // combinational sampling
  default clocking cb @(*); endclocking

  function automatic bit pwr_good();
    return (VPWR===1'b1 && VGND===1'b0 && VPB===1'b1 && VNB===1'b0);
  endfunction

  // Power pins must be valid
  assert property (pwr_good());

  // Functional equivalence (4-state)
  assert property (disable iff (!pwr_good())
                   Y === ((~(A1 & A2)) & (~(B1 & B2))));

  // Functional equivalence when inputs are known (2-state strong)
  assert property (disable iff (!pwr_good())
                   (!$isunknown({A1,A2,B1,B2})) |-> (Y == ((~(A1 & A2)) & (~(B1 & B2)))));

  // X-propagation: if inputs known, output must be known
  assert property (disable iff (!pwr_good())
                   (!$isunknown({A1,A2,B1,B2})) |-> !$isunknown(Y));

  // Structural stage checks
  assert property (disable iff (!pwr_good()) nand0_out   === ~(A1 & A2));
  assert property (disable iff (!pwr_good()) nand1_out   === ~(B1 & B2));
  assert property (disable iff (!pwr_good()) and0_out_Y  === (nand0_out & nand1_out));
  assert property (disable iff (!pwr_good()) Y           === and0_out_Y);

  // Simple coverage
  cover property (disable iff (!pwr_good()) Y==1'b0);
  cover property (disable iff (!pwr_good()) Y==1'b1);
  cover property (disable iff (!pwr_good()) nand0_out==1'b0);
  cover property (disable iff (!pwr_good()) nand0_out==1'b1);
  cover property (disable iff (!pwr_good()) nand1_out==1'b0);
  cover property (disable iff (!pwr_good()) nand1_out==1'b1);
  cover property (disable iff (!pwr_good()) $rose(Y));
  cover property (disable iff (!pwr_good()) $fell(Y));

  // Truth-partition coverage
  cover property (disable iff (!pwr_good()) ( A1 && A2 &&  B1 && B2) && (Y==1'b0)); // both pairs 11 -> Y=0
  cover property (disable iff (!pwr_good()) (!A1 || !A2) && (!B1 || !B2) && (Y==1'b1)); // neither pair 11 -> Y=1
  cover property (disable iff (!pwr_good()) ( A1 && A2) && (! (B1 && B2)) && (Y==1'b0));
  cover property (disable iff (!pwr_good()) (! (A1 && A2)) && (B1 && B2) && (Y==1'b0));
endmodule

// Bind into the DUT (accessing internal nets)
bind my_module my_module_sva u_my_module_sva (
  .Y(Y), .A1(A1), .A2(A2), .B1(B1), .B2(B2),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB),
  .nand0_out(nand0_out), .nand1_out(nand1_out), .and0_out_Y(and0_out_Y)
);