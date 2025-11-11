// SVA for vending_machine
// Bind into the DUT to access internal signals without modifying RTL.

module vm_sva;
  // We are in the scope of vending_machine via bind, so these names resolve.
  // Clock/reset
  default clocking cb @(posedge clk); endclocking

  // Guard for $past usage
  bit past_valid;
  always_ff @(posedge clk) past_valid <= !reset ? 1'b1 : 1'b0;

  // --------------------
  // Basic sanity
  // --------------------
  // Synchronous reset puts everything in known state
  assert property (@(posedge clk)
    reset |-> (state==IDLE && drink==COKE && press_count==0 && coin_count==0 && dispense==0)
  );

  // No X on key regs
  assert property (@(posedge clk)
    !$isunknown({state, drink, press_count, coin_count, dispense})
  );

  // Legal encodings only
  assert property (!reset |-> state inside {IDLE,WAITING,DISPENSING});
  assert property (!reset |-> drink inside {COKE,SPRITE,FANTA});

  // --------------------
  // FSM next-state behavior
  // --------------------
  // IDLE: next depends only on coin
  assert property (past_valid && state==IDLE |=> state == ($past(coin) ? WAITING : IDLE));

  // WAITING: priority press_count>=5 else if coin_count>=10 else stay
  assert property (state==WAITING && press_count>=5 |=> state==DISPENSING);
  assert property (state==WAITING && press_count<5 && coin_count>=10 |=> state==IDLE);
  assert property (state==WAITING && press_count<5 && coin_count<10 |=> state==WAITING);

  // DISPENSING -> IDLE unconditionally
  assert property (state==DISPENSING |=> state==IDLE);

  // --------------------
  // Counters
  // --------------------
  // In WAITING: exact +1 per cycle; otherwise: forced to 0
  assert property (past_valid && state==WAITING |=> press_count == $past(press_count)+1);
  assert property (state!=WAITING |=> press_count == 0);

  assert property (past_valid && state==WAITING |=> coin_count == $past(coin_count)+1);
  assert property (state!=WAITING |=> coin_count == 0);

  // --------------------
  // Output timing
  // --------------------
  // dispense reflects previous cycle's DISPENSING, and is a 1-cycle pulse
  assert property (past_valid |-> dispense == $past(state==DISPENSING));
  assert property (dispense |=> !dispense);

  // --------------------
  // Drink selection/update
  // --------------------
  // In IDLE and DISPENSING, next drink forced to COKE
  assert property (state==IDLE |=> drink==COKE);
  assert property (state==DISPENSING |=> drink==COKE);

  // In WAITING: update only on button; coin selects FANTA vs SPRITE
  assert property (state==WAITING && button &&  coin |=> drink==FANTA);
  assert property (state==WAITING && button && !coin |=> drink==SPRITE);
  assert property (past_valid && state==WAITING && !button |=> drink==$past(drink));

  // --------------------
  // Key functional coverage
  // --------------------
  // Nominal vend path: coin -> wait out -> dispense pulse
  cover property (state==IDLE && coin |=> state==WAITING ##5 state==DISPENSING ##1 dispense);

  // Selection updates
  cover property (state==WAITING && button && !coin |=> drink==SPRITE);
  cover property (state==WAITING && button &&  coin |=> drink==FANTA);

  // Attempt to cover the coin_count timeout path (likely unreachable)
  cover property (state==WAITING && press_count<5 && coin_count>=10 |=> state==IDLE);
endmodule

bind vending_machine vm_sva vm_sva_i();