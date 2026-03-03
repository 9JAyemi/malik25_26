// SVA for my_module: concise, high-quality checks and coverage

module my_module_sva (
  input logic X,
  input logic A,
  input logic SLEEP,
  input logic VPWR, VGND, VPB, VNB
);

  // Power-good gate
  wire pwr_ok = (VPWR===1'b1) && (VGND===1'b0) && (VPB===1'b1) && (VNB===1'b0);

  // Check supplies themselves (fires at time 0 and on any change)
  assert property (@(VPWR or VGND or VPB or VNB) pwr_ok)
    else $error("my_module: power pins not at expected values");

  default disable iff (!pwr_ok);

  // Functional equivalence: X == (A & ~SLEEP)
  assert property (@(posedge A or negedge A or posedge SLEEP or negedge SLEEP or posedge X or negedge X)
                   X === (A & ~SLEEP))
    else $error("my_module: X != (A & ~SLEEP)");

  // Sleep forces and holds 0 until deasserted
  assert property (@(posedge A or negedge A or posedge SLEEP or negedge SLEEP or posedge X or negedge X)
                   (SLEEP===1'b1) |-> (X===1'b0 until_with (SLEEP===1'b0)))
    else $error("my_module: X must hold 0 while SLEEP==1");

  // Awake pass-through when A is known
  assert property (@(posedge A or negedge A or posedge SLEEP or negedge SLEEP or posedge X or negedge X)
                   (SLEEP===1'b0 && !$isunknown(A)) |-> (X===A))
    else $error("my_module: pass-through failed when awake");

  // X can be 1 only if awake with A=1
  assert property (@(posedge X or posedge A or negedge A or posedge SLEEP or negedge SLEEP)
                   X===1'b1 |-> (SLEEP===1'b0 && A===1'b1))
    else $error("my_module: X high illegal when sleeping or A!=1");

  // Sanity: SLEEP must be known on its edges
  assert property (@(posedge SLEEP or negedge SLEEP) !$isunknown(SLEEP))
    else $error("my_module: SLEEP must not be X/Z");

  // Output knownness in guaranteed cases
  assert property (@(posedge A or negedge A or posedge SLEEP or negedge SLEEP)
                   (SLEEP===1'b1) |-> (X===1'b0 && !$isunknown(X)));
  assert property (@(posedge A or negedge A)
                   (SLEEP===1'b0 && !$isunknown(A)) |-> !$isunknown(X));

  // Coverage: exercise both modes and edges
  cover property (@(posedge SLEEP) X===1'b0);             // enter sleep
  cover property (@(negedge SLEEP) X===A);                // exit sleep
  cover property (@(posedge A) (SLEEP==1'b0 && X==1));    // awake rise
  cover property (@(negedge A) (SLEEP==1'b0 && X==0));    // awake fall
  cover property (@(posedge A) (SLEEP==1'b1 && X==0));    // A toggles during sleep
  cover property (@(posedge X));                          // X asserted at least once

endmodule

// Bind into the DUT (bind has access to internal supplies)
bind my_module my_module_sva u_my_module_sva (
  .X(X), .A(A), .SLEEP(SLEEP),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);