// SVA for circuit_design. Bind this to the DUT.
module circuit_design_sva (
  input X, A1, A2, A3, B1, VPWR, VGND, VPB, VNB
);
  // Power good
  wire pgood = (VPWR===1'b1) && (VGND===1'b0);

  // Functional correctness under known inputs
  // Equivalent boolean: X == (~A1 & (A2|A3)) when A1/A2/A3 are 0/1
  assert property (disable iff (!pgood)
                   !$isunknown({A1,A2,A3}) |-> X == ((~A1) & (A2|A3)));

  // Priority/forcing behavior (holds even if A2/A3 unknown)
  assert property (disable iff (!pgood) (A1===1'b1) |-> (X===1'b0));
  assert property (disable iff (!pgood) (A1===1'b0 && (A2===1'b1 || A3===1'b1)) |-> (X===1'b1));
  assert property (disable iff (!pgood) (A1===1'b0 && A2===1'b0 && A3===1'b0) |-> (X===1'b0));

  // Output must be known when inputs are known
  assert property (disable iff (!pgood) !$isunknown({A1,A2,A3}) |-> !$isunknown(X));

  // Unused input independence
  assert property (disable iff (!pgood) $changed(B1)  && !$changed({A1,A2,A3}) |-> !$changed(X));
  assert property (disable iff (!pgood) ($changed(VPB) || $changed(VNB)) && !$changed({A1,A2,A3}) |-> !$changed(X));

  // Body-bias pins tied to rails when powered
  assert property (pgood |-> (VPB===VPWR && VNB===VGND));

  // Basic functional coverage
  cover property (disable iff (!pgood) (A1==1 && X==0));                            // A1 forces 0
  cover property (disable iff (!pgood) (A1==0 && A2==1 && X==1));                   // A2 path
  cover property (disable iff (!pgood) (A1==0 && A2==0 && A3==1 && X==1));          // A3 path
  cover property (disable iff (!pgood) (A1==0 && A2==0 && A3==0 && X==0));          // default 0
  cover property (disable iff (!pgood) (A1==1 && (A2||A3) && X==0));                // priority over A2/A3
  cover property (disable iff (!pgood) $changed(B1) && !$changed({A1,A2,A3}));      // B1 toggled, A's stable
endmodule

bind circuit_design circuit_design_sva sva_i (.*);