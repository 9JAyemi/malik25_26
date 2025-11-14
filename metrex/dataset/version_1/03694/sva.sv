// SVA for sky130_fd_sc_hd__nor4
module sky130_fd_sc_hd__nor4_sva (
  input logic Y,
  input logic A, B, C, D,
  input logic VPWR, VGND, VPB, VNB
);

  default clocking cb @(A or B or C or D or Y or VPWR or VGND or VPB or VNB); endclocking

  function automatic bit powered_on();
    powered_on = (VPWR===1'b1) && (VGND===1'b0);
  endfunction

  // Body-bias/supply sanity
  assert property ( !$isunknown({VPB,VNB,VPWR,VGND}) |-> (VPB===VPWR && VNB===VGND) );
  assert property ( powered_on() |-> !$isunknown({VPWR,VGND}) );

  // Functional correctness (4-state aware)
  assert property ( powered_on() |-> ( Y === ~((A ~^ B) ~| (C ~^ D)) ) );

  // Output changes only when inputs change (under power)
  assert property ( powered_on() && $changed(Y) |-> $changed({A,B,C,D}) );

  // No X on output when inputs are known (under power)
  assert property ( powered_on() && !$isunknown({A,B,C,D}) |-> !$isunknown(Y) );

  // Coverage: output values under power with known inputs
  cover property ( powered_on() && !$isunknown({A,B,C,D}) && (Y==1'b0) );
  cover property ( powered_on() && !$isunknown({A,B,C,D}) && (Y==1'b1) );

  // Coverage: all AB and CD input combinations under power
  cover property ( powered_on() && !$isunknown({A,B}) && A===1'b0 && B===1'b0 );
  cover property ( powered_on() && !$isunknown({A,B}) && A===1'b0 && B===1'b1 );
  cover property ( powered_on() && !$isunknown({A,B}) && A===1'b1 && B===1'b0 );
  cover property ( powered_on() && !$isunknown({A,B}) && A===1'b1 && B===1'b1 );

  cover property ( powered_on() && !$isunknown({C,D}) && C===1'b0 && D===1'b0 );
  cover property ( powered_on() && !$isunknown({C,D}) && C===1'b0 && D===1'b1 );
  cover property ( powered_on() && !$isunknown({C,D}) && C===1'b1 && D===1'b0 );
  cover property ( powered_on() && !$isunknown({C,D}) && C===1'b1 && D===1'b1 );

  // Coverage: cause of Y values
  cover property ( powered_on() && !$isunknown({A,B,C,D}) && (A===B) && (C!==D) && (Y==1) );
  cover property ( powered_on() && !$isunknown({A,B,C,D}) && (A!==B) && (C===D) && (Y==1) );
  cover property ( powered_on() && !$isunknown({A,B,C,D}) && (A===B) && (C===D) && (Y==1) );
  cover property ( powered_on() && !$isunknown({A,B,C,D}) && (A!==B) && (C!==D) && (Y==0) );

endmodule

bind sky130_fd_sc_hd__nor4 sky130_fd_sc_hd__nor4_sva sva_i (.*);