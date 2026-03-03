// SVA for module_name
// Bind-in assertions; no DUT changes required.

module module_name_sva (
  input logic A1,
  input logic A2,
  input logic A3,
  input logic B1,
  input logic Y,
  input logic VPWR,
  input logic VGND,
  input logic VPB,
  input logic VNB
);

  // Sample on any activity of relevant nets
  default clocking cb @(
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge A3 or negedge A3 or
    posedge B1 or negedge B1 or
    posedge Y  or negedge Y  or
    posedge VPWR or negedge VPWR or
    posedge VGND or negedge VGND or
    posedge VPB  or negedge VPB  or
    posedge VNB  or negedge VNB
  ); endclocking

  // Convenience lets
  let pgood = (VPWR===1'b1 && VGND===1'b0 && VPB===1'b1 && VNB===1'b0);
  let t1   = (A1 & A2 & A3 & ~B1);
  let t2   = (~A1 & ~A2 & ~A3 & B1);

  // Rails must be correct whenever they change
  assert property (pgood)
    else $error("module_name: Power rails not at expected values");

  // Inputs should be known (optional: tighten or turn to assume in formal)
  assert property (disable iff (!pgood) !$isunknown({A1,A2,A3,B1}))
    else $error("module_name: Unknown on inputs");

  // If inputs are known, output must be known
  assert property (disable iff (!pgood) (!$isunknown({A1,A2,A3,B1}) |-> !$isunknown(Y)))
    else $error("module_name: Output unknown with known inputs");

  // Functional correctness: Y == (t1 || t2)
  assert property (disable iff (!pgood) (!$isunknown({A1,A2,A3,B1}) |-> (Y == (t1 || t2))))
    else $error("module_name: Functional mismatch Y vs A*,B1");

  // No spurious 1s: if Y==1 then exactly one cube is true
  assert property (disable iff (!pgood) (Y |-> (t1 || t2)))
    else $error("module_name: Y asserted without a valid cause");

  // Cubes are mutually exclusive
  assert property (disable iff (!pgood) !(t1 && t2))
    else $error("module_name: Mutually exclusive terms both true");

  // Coverage: exercise both 1-cases and a 0-case; also toggle Y
  cover property (disable iff (!pgood) (t1 && Y));
  cover property (disable iff (!pgood) (t2 && Y));
  cover property (disable iff (!pgood) (!$isunknown({A1,A2,A3,B1}) && !(t1||t2) && (Y==1'b0)));
  cover property (disable iff (!pgood) $rose(Y));
  cover property (disable iff (!pgood) $fell(Y));

endmodule

bind module_name module_name_sva sva_module_name (.*);