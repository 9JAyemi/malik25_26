// SVA for digital_circuit
// Bind into the DUT; no TB changes needed.
module digital_circuit_sva;

  // Convenience predicates
  function automatic bit rails_good();
    return (VPWR===1'b1 && VGND===1'b0 && VPB===1'b1 && VNB===1'b0);
  endfunction
  function automatic bit in_known();
    return !$isunknown({A1,A2,B1_N});
  endfunction

  // Drive assertions on any relevant input/power transition
  default clocking cb @(
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge B1_N or negedge B1_N or
    posedge VPWR or negedge VPWR or
    posedge VGND or negedge VGND or
    posedge VPB or negedge VPB or
    posedge VNB or negedge VNB
  ); endclocking

  // Functional correctness (powered, inputs known)
  assert property (rails_good() && in_known() |-> Y == (B1_N & (~A1 | ~A2)));

  // Output must be known when powered and inputs known
  assert property (rails_good() && in_known() |-> !$isunknown(Y));

  // Stability: if inputs are stable, output must be stable
  assert property (rails_good() && in_known() && $stable({A1,A2,B1_N}) |-> $stable(Y));

  // Structural sanity on internal nets (when their drivers are known)
  assert property (rails_good() && !$isunknown(B1_N)      |-> b                == ~B1_N);
  assert property (rails_good() && !$isunknown({A1,A2})   |-> and0_out         == (A1 & A2));
  assert property (rails_good() && !$isunknown({b,and0_out}) |-> nor0_out_Y       == ~(b | and0_out));
  assert property (rails_good() && !$isunknown(nor0_out_Y) |-> pwrgood_pp0_out_Y == nor0_out_Y);
  assert property (rails_good() && !$isunknown(pwrgood_pp0_out_Y) |-> Y == pwrgood_pp0_out_Y);

  // Corner implications (redundant to functional, but catch common slips)
  assert property (rails_good() && in_known() && (B1_N==1'b0) |-> Y==1'b0);
  assert property (rails_good() && in_known() && (A1 & A2)    |-> Y==1'b0);

  // Coverage: exercise all input combinations under good rails
  cover property (rails_good() && A1==0 && A2==0 && B1_N==0);
  cover property (rails_good() && A1==0 && A2==0 && B1_N==1);
  cover property (rails_good() && A1==0 && A2==1 && B1_N==0);
  cover property (rails_good() && A1==0 && A2==1 && B1_N==1);
  cover property (rails_good() && A1==1 && A2==0 && B1_N==0);
  cover property (rails_good() && A1==1 && A2==0 && B1_N==1);
  cover property (rails_good() && A1==1 && A2==1 && B1_N==0);
  cover property (rails_good() && A1==1 && A2==1 && B1_N==1);

  // Coverage: both output edges when powered
  cover property (rails_good() && in_known() && $rose(Y));
  cover property (rails_good() && in_known() && $fell(Y));

endmodule

bind digital_circuit digital_circuit_sva sva_inst();