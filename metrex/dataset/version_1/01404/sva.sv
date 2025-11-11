// SVA bind module for sky130_fd_sc_ls__o21ai
// Focus: functional correctness under power-good, X-propagation, and basic power-tie checks.

module sky130_fd_sc_ls__o21ai_sva (
  input logic A1,
  input logic A2,
  input logic B1,
  input logic Y,
  input logic VPB,
  input logic VPWR,
  input logic VGND,
  input logic VNB
);

  // Sample on any relevant activity (combinational cell)
  default clocking cb @ (A1 or A2 or B1 or Y or VPWR or VGND or VPB or VNB); endclocking

  // Power-good definition (4-state aware)
  wire pg = (VPWR === 1'b1) && (VGND === 1'b0) && (VPB === 1'b1) && (VNB === 1'b0);

  // Spec function (do not mirror DUT ternary to avoid vacuous self-check):
  // Y = (~B1 & (A1 ^ A2)) | (B1 & A1 & A2)
  wire spec_y = ((~B1) & (A1 ^ A2)) | (B1 & A1 & A2);

  // Basic power-tie consistency checks
  assert property ( (VPWR === 1'b1) |-> (VPB === 1'b1) )
    else $error("VPB must be tied high when VPWR is high");
  assert property ( (VGND === 1'b0) |-> (VNB === 1'b0) )
    else $error("VNB must be tied low when VGND is low");

  // Functional correctness when all inputs known and power good
  assert property ( pg && !$isunknown({A1,A2,B1}) |-> (Y === spec_y) )
    else $error("Functional mismatch to spec_y under power-good with known inputs");

  // Deterministic corner cases (power good)
  // A1=A2=0 => Y=0 regardless of B1
  assert property ( pg && (A1 === 1'b0) && (A2 === 1'b0) |-> (Y === 1'b0) )
    else $error("A1=A2=0 must force Y=0 under power-good");

  // A1=A2=1 => Y=B1 (propagates B1 and its X)
  assert property ( pg && (A1 === 1'b1) && (A2 === 1'b1) && !$isunknown(B1) |-> (Y === B1) )
    else $error("A1=A2=1 must pass B1 under power-good with known B1");
  assert property ( pg && (A1 === 1'b1) && (A2 === 1'b1) &&  $isunknown(B1) |->  $isunknown(Y) )
    else $error("A1=A2=1 must propagate X from B1 under power-good");

  // Exactly one of A1/A2 is 1 => Y = ~B1 (propagates X on B1)
  assert property ( pg && ((A1 ^ A2) === 1'b1) && !$isunknown(B1) |-> (Y === ~B1) )
    else $error("When A1^A2=1, Y must be ~B1 under power-good with known B1");
  assert property ( pg && ((A1 ^ A2) === 1'b1) &&  $isunknown(B1) |->  $isunknown(Y) )
    else $error("When A1^A2=1, Y must propagate X from B1 under power-good");

  // No X on Y when inputs are all known and power good
  assert property ( pg && !$isunknown({A1,A2,B1}) |-> !$isunknown(Y) )
    else $error("Y must be known when inputs are known under power-good");

  // Combinational stability: if inputs stable, Y should be stable
  assert property ( pg && $stable({A1,A2,B1}) |-> $stable(Y) )
    else $error("Y changed without input change under power-good");

  // Coverage: power-good observed
  cover property ( pg );

  // Coverage: all functional cubes
  cover property ( pg && (A1===1'b0) && (A2===1'b0) && (Y===1'b0) );
  cover property ( pg && (A1===1'b1) && (A2===1'b1) && (B1===1'b0) && (Y===1'b0) );
  cover property ( pg && (A1===1'b1) && (A2===1'b1) && (B1===1'b1) && (Y===1'b1) );
  cover property ( pg && ((A1^A2)===1'b1) && (B1===1'b0) && (Y===1'b1) );
  cover property ( pg && ((A1^A2)===1'b1) && (B1===1'b1) && (Y===1'b0) );

  // Coverage: X-propagation scenarios that should produce Y=X
  cover property ( pg && ((A1^A2)===1'b1) && $isunknown(B1) && $isunknown(Y) );
  cover property ( pg && (A1===1'b1) && (A2===1'b1) && $isunknown(B1) && $isunknown(Y) );

endmodule

// Bind into the DUT
bind sky130_fd_sc_ls__o21ai sky130_fd_sc_ls__o21ai_sva u_sva (
  .A1(A1),
  .A2(A2),
  .B1(B1),
  .Y (Y),
  .VPB(VPB),
  .VPWR(VPWR),
  .VGND(VGND),
  .VNB(VNB)
);