// SVA for my_module
// Bind into the DUT to check internal nets and final output under good power
module my_module_sva (
  input logic A1, A2, A3, B1,
  input logic VPWR, VGND, VPB, VNB,
  input logic or0_out, nand0_out_Y,
  input logic Y
);

  function automatic bit pwr_good();
    return (VPWR === 1'b1 && VGND === 1'b0 && VPB === 1'b1 && VNB === 1'b0);
  endfunction

  function automatic bit inputs_known();
    return !$isunknown({A1,A2,A3,B1});
  endfunction

  let OR3 = (A1 | A2 | A3);
  let EXP = ~(B1 & OR3);

  // Structural/functional equivalence under good rails and known inputs
  assert property (disable iff (!(pwr_good() && inputs_known())) or0_out     === OR3);
  assert property (disable iff (!(pwr_good() && inputs_known())) nand0_out_Y === ~(B1 & or0_out));
  assert property (disable iff (!(pwr_good() && inputs_known())) Y           === EXP);
  assert property (disable iff (!(pwr_good() && inputs_known())) !$isunknown({or0_out, nand0_out_Y, Y}));

  // Minimal, high-value coverage
  cover property (pwr_good() && inputs_known() && !B1           && Y == 1'b1);          // B1 forces high
  cover property (pwr_good() && inputs_known() && (OR3 == 1'b0) && Y == 1'b1);          // OR=0 forces high
  cover property (pwr_good() && inputs_known() && (B1 && OR3)   && Y == 1'b0);          // Only low corner
  cover property (pwr_good() && inputs_known() && $rose(Y));                             
  cover property (pwr_good() && inputs_known() && $fell(Y));
  cover property (pwr_good() && inputs_known() && $rose(B1) && OR3 && $fell(Y));        // Falling due to B1
  cover property (pwr_good() && inputs_known() && $rose(OR3) && B1 && $fell(Y));        // Falling due to OR
  cover property (pwr_good() && inputs_known() && $fell(B1) && $rose(Y));               // Rising due to B1
  cover property (pwr_good() && inputs_known() && $fell(OR3) && B1 && $rose(Y));        // Rising due to OR
  cover property (pwr_good());                                                          // Rails good seen

endmodule

bind my_module my_module_sva sva_my_module (
  .A1(A1), .A2(A2), .A3(A3), .B1(B1),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB),
  .or0_out(or0_out), .nand0_out_Y(nand0_out_Y),
  .Y(Y)
);