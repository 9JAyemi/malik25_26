// SVA for vending_machine
// Bind this checker to the DUT: bind vending_machine vending_machine_sva sva();

module vending_machine_sva;

  // Access bound instance signals/params directly
  default clocking cb @(posedge clk); endclocking

  // Basic safety: at most one dispense output high at any time
  ap_onehot_outputs: assert property ($onehot0({dispenseBar,dispenseChips,dispenseSoda}));

  // No spurious dispense: any dispense must be caused by a prior IDLE+button press (with priority)
  ap_dispense_has_cause: assert property (
    (dispenseBar || dispenseChips || dispenseSoda) |->
      ($past(state)==IDLE && ($past(btnA)||$past(btnB)||$past(btnC)))
  );

  // Priority and mapping from prior-cycle inputs in IDLE to current outputs and next state
  ap_A_maps: assert property (
    $past(state)==IDLE && $past(btnA) |->
      (dispenseBar && !dispenseChips && !dispenseSoda && state==DISPENSING)
  );
  ap_B_maps: assert property (
    $past(state)==IDLE && !$past(btnA) && $past(btnB) |->
      (!dispenseBar && dispenseChips && !dispenseSoda && state==DISPENSING)
  );
  ap_C_maps: assert property (
    $past(state)==IDLE && !$past(btnA) && !$past(btnB) && $past(btnC) |->
      (!dispenseBar && !dispenseChips && dispenseSoda && state==DISPENSING)
  );

  // No buttons in IDLE -> no dispense and stay in IDLE
  ap_idle_hold: assert property (
    $past(state)==IDLE && !$past(btnA||btnB||btnC) |->
      (!dispenseBar && !dispenseChips && !dispenseSoda && state==IDLE)
  );

  // Single-cycle pulses: any dispense deasserts next cycle
  ap_pulse_one_cycle: assert property (
    $past(dispenseBar || dispenseChips || dispenseSoda) |->
      (!dispenseBar && !dispenseChips && !dispenseSoda)
  );

  // Outputs must be 0 during DISPENSING/RESET phases (observed one cycle later)
  ap_nonidle_no_outputs: assert property (
    $past(state)!=IDLE |->
      (!dispenseBar && !dispenseChips && !dispenseSoda)
  );

  // FSM next-state relations
  ap_ns_idle_to_disp: assert property (
    $past(state)==IDLE && $past(btnA||btnB||btnC) |-> state==DISPENSING
  );
  ap_ns_disp_to_reset: assert property (
    $past(state)==DISPENSING |-> state==RESET
  );
  ap_ns_reset_to_idle: assert property (
    $past(state)==RESET |-> state==IDLE
  );

  // Entering DISPENSING must come from IDLE
  ap_disp_from_idle: assert property (state==DISPENSING |-> $past(state)==IDLE);

  // Illegal encoding self-recovery: any illegal state recovers to IDLE next cycle with no dispense
  ap_illegal_recover: assert property (
    !($past(state) inside {IDLE,DISPENSING,RESET}) |->
      (state==IDLE && !dispenseBar && !dispenseChips && !dispenseSoda)
  );

  // Reverse-causality mapping: which button caused which dispense (with priority)
  ap_bar_caused_by_A: assert property (
    dispenseBar |->
      ($past(state)==IDLE && $past(btnA))
  );
  ap_chips_caused_by_B: assert property (
    dispenseChips |->
      ($past(state)==IDLE && !$past(btnA) && $past(btnB))
  );
  ap_soda_caused_by_C: assert property (
    dispenseSoda |->
      ($past(state)==IDLE && !$past(btnA) && !$past(btnB) && $past(btnC))
  );

  // Coverage: each product dispensed
  cv_bar:   cover property ($past(state)==IDLE && $past(btnA)                              && dispenseBar);
  cv_chips: cover property ($past(state)==IDLE && !$past(btnA) && $past(btnB)              && dispenseChips);
  cv_soda:  cover property ($past(state)==IDLE && !$past(btnA) && !$past(btnB) && $past(btnC) && dispenseSoda);

  // Coverage: priority cases
  cv_AB:   cover property ($past(state)==IDLE && $past(btnA) && $past(btnB)                && dispenseBar);
  cv_AC:   cover property ($past(state)==IDLE && $past(btnA) && $past(btnC)                && dispenseBar);
  cv_BC:   cover property ($past(state)==IDLE && !$past(btnA) && $past(btnB) && $past(btnC) && dispenseChips);
  cv_ABC:  cover property ($past(state)==IDLE && $past(btnA) && $past(btnB) && $past(btnC) && dispenseBar);

  // Coverage: full dispense cycle sequencing
  cv_full_cycle: cover property ( (state==IDLE && (btnA||btnB||btnC)) |=> state==DISPENSING ##1 state==RESET ##1 state==IDLE );

  // Coverage: illegal state recovery (useful given no explicit reset)
  cv_illegal_recovery: cover property ( !(state inside {IDLE,DISPENSING,RESET}) |=> state==IDLE );

endmodule