// SVA for Latch: 1-cycle delayed D to Q with complementary Q_bar
// Bind into the DUT to access internal D_prev
module Latch_sva (
  input logic D, CLK, Q, Q_bar,
  input logic D_prev
);
  default clocking cb @ (posedge CLK); endclocking

  // Functional correctness: 1-cycle delay and complement, post-NBA (##0)
  property p_delay_and_complement;
    !$isunknown($past(D)) |-> ##0 (Q === $past(D) && Q_bar === ~ $past(D));
  endproperty
  assert property (p_delay_and_complement);

  // Internal state update: D_prev captures D on the same clock (post-NBA)
  assert property (##0 (D_prev === D));

  // Outputs are always complementary (post-NBA)
  assert property (##0 (Q_bar === ~Q));

  // No X/Z on outputs after first valid cycle
  assert property (!$isunknown($past(D)) |-> ##0 !$isunknown({Q,Q_bar}));

  // Outputs only change on clock rising edge (no mid-cycle glitches)
  assert property (@(posedge Q) $rose(CLK));
  assert property (@(negedge Q) $rose(CLK));
  assert property (@(posedge Q_bar) $rose(CLK));
  assert property (@(negedge Q_bar) $rose(CLK));

  // Coverage
  cover property (##0 (Q==0 && Q_bar==1));
  cover property (##0 (Q==1 && Q_bar==0));
  cover property (!$isunknown($past(D)) && ##0 (Q !== $past(Q))); // Q toggles
  cover property ($past(D)==0 && D==1); // D rising
  cover property ($past(D)==1 && D==0); // D falling
endmodule

bind Latch Latch_sva Latch_sva_i (
  .D(D), .CLK(CLK), .Q(Q), .Q_bar(Q_bar), .D_prev(D_prev)
);