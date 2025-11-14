// SVA checkers and binds for SR_FF_D_FFSR_MUX and sub-blocks

// ---------------- D_FF_SR checker ----------------
module D_FF_SR_chk;
  // Use the DUT's own ports/signals in this scope
  default clocking cb @ (posedge CLK); endclocking

  // Priority and next-state behavior
  assert property (R |-> Q == 1'b0);
  assert property (!R && S |-> Q == 1'b1);
  assert property (!R && !S |-> Q == $past(D));

  // Explicit R over S priority when both 1
  assert property (R && S |-> Q == 1'b0);

  // Q must be stable between rising edges (no glitches)
  assert property (1 |-> $stable(Q) until_with $rose(CLK));

  // Coverage: hit each behavior on a clock
  cover property (R);
  cover property (!R && S);
  cover property (!R && !S && (D != $past(D)));
endmodule
bind D_FF_SR D_FF_SR_chk dff_sr_chk();

// ---------------- MUX2x1 checker ----------------
module MUX2x1_chk;
  // Check functionality whenever any input can affect output
  // (use a broad sensitivity for near-continuous checking)
  assert property (@(posedge IN0 or negedge IN0 or
                     posedge IN1 or negedge IN1 or
                     posedge SEL or negedge SEL)
                   OUT == (SEL ? IN1 : IN0));

  // Coverage: exercise both select paths and both data values
  cover property (@(posedge SEL)  OUT == IN1);
  cover property (@(negedge SEL)  OUT == IN0);
  cover property (@(posedge IN0) !SEL && (OUT == IN0));
  cover property (@(posedge IN1)  SEL && (OUT == IN1));
endmodule
bind MUX2x1 MUX2x1_chk mux2x1_chk();

// ---------------- Top-level composition checker ----------------
module SR_FF_D_FFSR_MUX_chk;
  // Access internal nets D_FF_Q and MUX_OUT in this scope
  // Combination correctness: Q is inversion of mux output
  assert property (@(posedge D_FF_Q or negedge D_FF_Q or
                     posedge S      or negedge S      or
                     posedge R      or negedge R      or
                     posedge CLK    or negedge CLK)
                   Q === ~MUX_OUT);

  // MUX function matches select and data sources
  assert property (@(posedge D_FF_Q or negedge D_FF_Q or
                     posedge S      or negedge S      or
                     posedge R      or negedge R)
                   MUX_OUT == (S ? R : D_FF_Q));

  // When S=1, Q follows ~R immediately; when S=0, Q follows ~D_FF_Q
  assert property (@(posedge R or negedge R or posedge S or negedge S)
                   S |-> (Q == ~R));
  assert property (@(posedge D_FF_Q or negedge D_FF_Q or posedge S or negedge S)
                   !S |-> (Q == ~D_FF_Q));

  // Q should only change between clocks due to S/R path (not due to D_FF_Q glitches)
  // D_FF_Q is already checked glitch-free; this ensures path partitioning is respected
  default clocking cb @ (posedge CLK); endclocking
  assert property (1 |-> ((S) -> $stable(D_FF_Q)) until_with $rose(CLK));

  // Coverage: exercise key modes and transitions
  //  - synchronous R priority when S=1 at a clock
  cover property (@(posedge CLK) (R && S) ##0 (Q == ~R));
  //  - S=1 mux path toggling via R
  cover property (@(posedge R)   S && (Q == ~R));
  cover property (@(negedge R)   S && (Q == ~R));
  //  - S=0 DFF path causes Q to toggle across clocks when D toggles
  cover property (@(posedge CLK) !S && !R ##1 !S && !R && (Q != $past(Q)));
endmodule
bind SR_FF_D_FFSR_MUX SR_FF_D_FFSR_MUX_chk top_chk();