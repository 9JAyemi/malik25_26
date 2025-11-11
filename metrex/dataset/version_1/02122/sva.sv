// SVA for my_module: NOR functional check, power-awareness, concise coverage
module my_module_sva (
  input X, A1, A2, B1, C1, VPWR, VGND, VPB, VNB
);

  function automatic bit power_good();
    return (VPWR===1'b1) && (VGND===1'b0) && (VPB===1'b1) && (VNB===1'b0);
  endfunction

  // Functional NOR correctness when powered and inputs known (avoid preponed race via ##0)
  property p_nor_func;
    @(A1 or A2 or VPWR or VGND or VPB or VNB)
      power_good() && !$isunknown({A1,A2}) |-> ##0 (X === ~(A1 | A2));
  endproperty
  assert property (p_nor_func);

  // X must be known when powered and inputs known
  property p_x_not_unknown;
    @(A1 or A2 or VPWR or VGND or VPB or VNB or X)
      power_good() && !$isunknown({A1,A2}) |-> ##0 !$isunknown(X);
  endproperty
  assert property (p_x_not_unknown);

  // Coverage: full truth table under good power
  cover property (@(A1 or A2) power_good() && A1===1'b0 && A2===1'b0 ##0 X===1'b1);
  cover property (@(A1 or A2) power_good() && A1===1'b1 && A2===1'b0 ##0 X===1'b0);
  cover property (@(A1 or A2) power_good() && A1===1'b0 && A2===1'b1 ##0 X===1'b0);
  cover property (@(A1 or A2) power_good() && A1===1'b1 && A2===1'b1 ##0 X===1'b0);

  // Coverage: input edge effects when the other input is 0 (shows active control of X)
  cover property (@(posedge A1) power_good() && A2===1'b0 ##0 X===1'b0);
  cover property (@(negedge A1) power_good() && A2===1'b0 ##0 X===1'b1);
  cover property (@(posedge A2) power_good() && A1===1'b0 ##0 X===1'b0);
  cover property (@(negedge A2) power_good() && A1===1'b0 ##0 X===1'b1);

  // Coverage: power becoming good at least once
  cover property (@(VPWR or VGND or VPB or VNB) power_good());

  // Coverage: unused pins toggle under good power (X insensitivity is implied by p_nor_func)
  cover property (@(B1) power_good());
  cover property (@(C1) power_good());

endmodule

bind my_module my_module_sva
  (.X(X), .A1(A1), .A2(A2), .B1(B1), .C1(C1), .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB));