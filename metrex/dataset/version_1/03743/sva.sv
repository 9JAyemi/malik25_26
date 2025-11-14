// SVA for sync_resettable_latch
module sync_resettable_latch_sva(
  input logic        CLK,
  input logic        EN,
  input logic        RST,
  input logic [3:0]  D,
  input logic [3:0]  Q
);

  // Basic past-valid guard
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge CLK) past_valid <= 1'b1;

  default clocking cb @(posedge CLK); endclocking
  default disable iff (!past_valid);

  // Golden next-state functional spec (EN has priority over RST; sync behavior)
  property next_state_spec;
    !$isunknown({$past(EN), $past(RST)}) |-> 
      (Q === ($past(EN) ? $past(D) : ($past(RST) ? 4'b0 : $past(Q))));
  endproperty
  assert property (next_state_spec);

  // Explicit priority check when EN and RST are both 1
  assert property ( $past(EN) && $past(RST) |-> (Q == $past(D)) );

  // Output is stable between clocks (no half-cycle glitches)
  assert property ( @(negedge CLK) $stable(Q) );

  // Coverage: exercise all behavioral modes and effects
  cover property ( $past(EN) && !$past(RST) && (Q == $past(D)) );                 // data capture
  cover property ( !$past(EN) && $past(RST) && (Q == 4'b0) );                     // reset action
  cover property ( $past(EN) && $past(RST) && (Q == $past(D)) );                  // priority case
  cover property ( !$isunknown($past(Q)) && !$past(EN) && !$past(RST) && (Q == $past(Q)) ); // hold
  cover property ( $past(EN) && (Q != $past(Q)) );                                 // Q changes due to EN
  cover property ( !$past(EN) && $past(RST) && ($past(Q) != 4'b0) && (Q == 4'b0) );// Q driven to 0 by RST

endmodule

bind sync_resettable_latch sync_resettable_latch_sva u_sync_resettable_latch_sva (.*);