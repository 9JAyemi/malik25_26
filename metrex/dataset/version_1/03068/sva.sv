// SVA checker for my_module
// Function: X == (A1 & A2 & A3) | B1, when power rails are good.
// Bind this to the DUT instance.

module my_module_sva (
  input X,
  input A1, A2, A3, B1,
  input VPWR, VGND, VPB, VNB
);

  // Power-good and helpers
  wire pgood         = (VPWR === 1'b1) && (VGND === 1'b0);
  wire inputs_known  = !$isunknown({A1,A2,A3,B1});
  wire and_term      = A1 & A2 & A3;
  wire func          = and_term | B1;

  // Sample on any relevant edge
  default clocking cb @(
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge A3 or negedge A3 or
    posedge B1 or negedge B1 or
    posedge X  or negedge X  or
    posedge VPWR or negedge VPWR or
    posedge VGND or negedge VGND
  ); endclocking

  // Rail/body-tie checks (active only when rails are good)
  assert property (disable iff (!pgood) (VPB === VPWR && VNB === VGND))
    else $error("Body ties not connected to rails when power-good");

  // No X on output when inputs are known and rails are good
  assert property (disable iff (!pgood) (inputs_known |-> !$isunknown(X)))
    else $error("X is unknown with known inputs and power-good");

  // Functional equivalence
  assert property (disable iff (!pgood) (inputs_known |-> ##0 (X === func)))
    else $error("Functional mismatch: X != (A1&A2&A3)|B1");

  // Dominance/special cases (concise sanity)
  assert property (disable iff (!pgood) (B1 === 1'b1 |-> X === 1'b1))
    else $error("B1 high must force X high");
  assert property (disable iff (!pgood) (B1 === 1'b0 |-> X === and_term))
    else $error("When B1=0, X must equal A1&A2&A3");

  // No spurious output changes without input change
  assert property (disable iff (!pgood) ($stable({A1,A2,A3,B1}) |-> $stable(X)))
    else $error("X changed without input change");

  // Minimal, targeted coverage
  cover property (pgood && !B1 &&  A1 &&  A2 &&  A3 &&  X); // AND path drives high
  cover property (pgood &&  B1 && !and_term &&  X);         // OR path (B1) drives high
  cover property (pgood && !B1 && !A1 && !A2 && !A3 && !X); // All low -> X low
  cover property (pgood && $rose(B1)            && $rose(X));
  cover property (pgood && !$past(B1) && $rose(and_term) && $rose(X));
  cover property (pgood && $fell(B1 | and_term) && $fell(X));

endmodule

// Bind into DUT
bind my_module my_module_sva my_module_sva_i (
  .X(X), .A1(A1), .A2(A2), .A3(A3), .B1(B1),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);