// SVA for my_module (concise, full functional coverage)
// Bind this file; no DUT or TB changes needed.

module my_module_sva (
  input logic Y,
  input logic A1, A2, A3, A4, B1,
  input logic VPWR, VGND, VPB, VNB
);

  // Sample on any edge of relevant signals
  clocking cb @(
      posedge A1 or negedge A1 or
      posedge A2 or negedge A2 or
      posedge A3 or negedge A3 or
      posedge A4 or negedge A4 or
      posedge B1 or negedge B1 or
      posedge VPWR or negedge VPWR or
      posedge VGND or negedge VGND or
      posedge VPB  or negedge VPB  or
      posedge VNB  or negedge VNB
  ); endclocking
  default clocking cb;

  // Useful lets
  let c1    = (B1 & ~VPWR);     // select A1^A2
  let c2    = (~B1);            // select 0
  let c3    = (B1 & VPWR);      // select A3^A4
  let y_exp = c1 ? (A1^A2) : (c2 ? 1'b0 : (A3^A4));

  // Functional equivalence (4-state)
  assert property (Y === y_exp)
    else $error("Y mismatch");

  // Exactly one branch when B1,VPWR are known
  assert property (!$isunknown({B1,VPWR}) |-> $onehot({c1,c2,c3}))
    else $error("Branch select not onehot");

  // No X on Y when rails valid and inputs known
  assert property ((VPWR===1 && VGND===0 && VPB===VPWR && VNB===VGND &&
                    !$isunknown({A1,A2,A3,A4,B1})) |-> !$isunknown(Y))
    else $error("Y unknown under valid rails");

  // Unused rails must not affect Y if functional inputs and VPWR stable
  assert property (($changed({VGND,VPB,VNB}) && $stable({A1,A2,A3,A4,B1,VPWR})) |=> Y==$past(Y))
    else $error("Y changed due to unused rail pin");

  // Branch coverage
  cover property (B1===1 && VPWR===0 && Y===(A1^A2));
  cover property (B1===0 && Y===1'b0);
  cover property (B1===1 && VPWR===1 && Y===(A3^A4));

  // Output toggle coverage under valid rails
  cover property (VPWR===1 && VGND===0 && $rose(Y));
  cover property (VPWR===1 && VGND===0 && $fell(Y));

  // Reach valid-rails condition
  cover property (VPWR===1 && VGND===0 && VPB===VPWR && VNB===VGND);

endmodule

// Bind to DUT
bind my_module my_module_sva my_module_sva_i (.*);