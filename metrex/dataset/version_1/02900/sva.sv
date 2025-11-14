// SVA for binary_latch_with_reset
// Checks synchronous reset and D->Q transfer; includes basic integrity and coverage.

module binary_latch_with_reset_sva(input CLK, input RST, input D, input Q);
  default clocking cb @(posedge CLK); endclocking

  bit past_valid;
  always @(posedge CLK) past_valid <= 1'b1;

  // Known/clean signals
  assert property (cb !$isunknown({RST, D}));
  assert property (cb past_valid |-> !$isunknown(Q));

  // Functional next-state: Q follows D when not resetting; reset dominates
  assert property (cb past_valid |-> Q == ( $past(RST) ? 1'b0 : $past(D)));

  // Q only changes on a clock rising edge (no glitches)
  assert property ( $changed(Q) |-> $rose(CLK) );

  // Coverage
  cover property (cb past_valid && $past(RST) && Q == 1'b0);                   // took reset
  cover property (cb past_valid && $past(!RST) && Q == 1'b0);                  // captured 0
  cover property (cb past_valid && $past(!RST) && Q == 1'b1);                  // captured 1
  cover property (cb past_valid && $past(!RST) && $past(Q)==0 && Q==1);        // 0->1 toggle
  cover property (cb past_valid && $past(!RST) && $past(Q)==1 && Q==0);        // 1->0 toggle
endmodule

bind binary_latch_with_reset binary_latch_with_reset_sva u_sva(.CLK(CLK), .RST(RST), .D(D), .Q(Q));