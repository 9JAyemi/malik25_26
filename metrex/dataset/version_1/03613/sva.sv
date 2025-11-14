// SVA for sky130_fd_sc_lp__dfxtp (positive-edge DFF with power pins)
// Focused, concise checks and coverage. Bind to the DUT.

module sky130_fd_sc_lp__dfxtp_sva (
  input D, Q, CLK, VPB, VPWR, VGND, VNB
);

  // Power-good qualification
  let PWR_GOOD = (VPWR===1'b1 && VGND===1'b0 && VPB===1'b1 && VNB===1'b0);

  default clocking cb @(posedge CLK); endclocking

  // Core functional behavior: one-cycle storage/capture
  // Avoids first-cycle $past issues via |=>.
  assert property (disable iff (!PWR_GOOD)
                   1 |=> Q == $past(D));

  // Known-value propagation: if D is known at a capture edge, Q is known by next edge
  assert property (disable iff (!PWR_GOOD)
                   !$isunknown(D) |=> !$isunknown(Q));

  // Q only changes on CLK rising edge (glitch-free output)
  assert property (@(posedge Q) disable iff (!PWR_GOOD) $rose(CLK));
  assert property (@(negedge Q) disable iff (!PWR_GOOD) $rose(CLK));

  // Coverage: capture 0 and 1, and observe Q activity/toggling and D→Q transfer
  cover property (disable iff (!PWR_GOOD) D==1'b0 ##1 Q==1'b0);
  cover property (disable iff (!PWR_GOOD) D==1'b1 ##1 Q==1'b1);
  cover property (disable iff (!PWR_GOOD) $rose(Q));
  cover property (disable iff (!PWR_GOOD) $fell(Q));
  cover property (disable iff (!PWR_GOOD) (D != $past(D)) ##1 (Q != $past(Q)));

endmodule

// Bind into the DUT
bind sky130_fd_sc_lp__dfxtp sky130_fd_sc_lp__dfxtp_sva sva_i (.*);