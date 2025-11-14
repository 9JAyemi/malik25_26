// SVA checker for d_ff_reset
module d_ff_reset_sva (
  input logic D, RESET_B, VPWR, VGND, VPB, VNB, CLK_N, Q,
  input logic D_valid, RESET_B_valid, VPWR_valid, VGND_valid, VPB_valid, VNB_valid
);

  // Power-good helper (4-state robust)
  logic power_good;
  assign power_good = (VPWR === 1'b1) && (VGND === 1'b0);

  // Sanity: internal valid qualifiers match power_good
  assert property (@(posedge CLK_N)
    (D_valid == power_good) &&
    (RESET_B_valid == power_good) &&
    (VPWR_valid == power_good) &&
    (VGND_valid == power_good)
  );

  // Synchronous, active-low reset drives Q=0 on the clock edge (reset has priority)
  assert property (@(posedge CLK_N)
    power_good && !RESET_B |-> ##0 (Q == 1'b0)
  );

  // When not in reset and power is good, Q captures D on the clock edge
  assert property (@(posedge CLK_N)
    power_good && RESET_B |-> ##0 (Q == D)
  );

  // No state update when power is not good
  assert property (@(posedge CLK_N)
    !power_good |-> (Q == $past(Q))
  );

  // Reset is synchronous: falling RESET_B does not change Q until next posedge
  assert property (
    $fell(RESET_B) && power_good |-> $stable(Q) until_with $rose(CLK_N)
  );

  // Q only changes on a clock posedge when power is good
  assert property (
    $changed(Q) |-> ($rose(CLK_N) && power_good)
  );

  // No glitches between clock edges
  assert property (@(negedge CLK_N) $stable(Q));

  // X-safety under valid operation
  assert property (@(posedge CLK_N)
    power_good && !RESET_B |-> ##0 !$isunknown(Q)
  );
  assert property (@(posedge CLK_N)
    power_good && RESET_B && !$isunknown(D) |-> ##0 !$isunknown(Q)
  );

  // Coverage
  cover property (@(posedge CLK_N) power_good);                       // power good observed
  cover property (@(posedge CLK_N) power_good && !RESET_B ##0 Q==0);  // reset event
  cover property (@(posedge CLK_N) power_good && RESET_B && $changed(D)); // data change under capture
  cover property (@(posedge CLK_N) power_good && RESET_B ##1 power_good && RESET_B && $changed(Q)); // Q captured change
  cover property (@(posedge CLK_N) !power_good ##1 !power_good && $stable(Q)); // hold while no power
  cover property (@(posedge CLK_N) power_good && !RESET_B && (D==1'b1) ##0 (Q==1'b0)); // reset priority over D
endmodule

// Bind into the DUT (accesses internal *_valid nets)
bind d_ff_reset d_ff_reset_sva sva (
  .D(D), .RESET_B(RESET_B), .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB), .CLK_N(CLK_N), .Q(Q),
  .D_valid(D_valid), .RESET_B_valid(RESET_B_valid), .VPWR_valid(VPWR_valid), .VGND_valid(VGND_valid),
  .VPB_valid(VPB_valid), .VNB_valid(VNB_valid)
);