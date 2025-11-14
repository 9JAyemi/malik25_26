// SVA for traffic_light_controller
// Binds into the DUT and checks sequencing, timing, outputs, and coverage.

module traffic_light_controller_sva;
  // Bind context provides direct access to DUT signals/params
  default clocking cb @(posedge clk); endclocking

  function automatic bit legal_state (logic [3:0] s);
    return (s == GREEN) || (s == YELLOW) || (s == RED);
  endfunction

  // Output must be a legal one-hot encoding when known
  ap_light_onehot: assert property ( !$isunknown(traffic_light) |-> 
                                     ((traffic_light inside {GREEN,YELLOW,RED}) && $onehot(traffic_light)) );

  // Output must mirror state encoding
  ap_state_out_g: assert property ( state == GREEN  |-> traffic_light == GREEN  );
  ap_state_out_y: assert property ( state == YELLOW |-> traffic_light == YELLOW );
  ap_state_out_r: assert property ( state == RED    |-> traffic_light == RED    );

  // If state ever goes illegal, recover to GREEN next cycle
  ap_illegal_recover: assert property ( !legal_state(state) |=> state == GREEN );

  // Counter bounds while in each state (prevents overflow within a phase)
  ap_count_bounds_g: assert property ( state == GREEN  |-> count <= 10 );
  ap_count_bounds_y: assert property ( state == YELLOW |-> count <= 2  );
  ap_count_bounds_r: assert property ( state == RED    |-> count <= 10 );

  // In-state hold: while below terminal count, stay in state and increment by 1
  ap_hold_g: assert property ( (state == GREEN  && count < 10) |=> (state == GREEN  && count == $past(count,1,0)+1) );
  ap_hold_y: assert property ( (state == YELLOW && count < 2 ) |=> (state == YELLOW && count == $past(count,1,0)+1) );
  ap_hold_r: assert property ( (state == RED    && count < 10) |=> (state == RED    && count == $past(count,1,0)+1) );

  // Transitions at terminal counts with counter reset to 0 in next state
  ap_tran_g: assert property ( (state == GREEN  && count == 10) |=> (state == YELLOW && count == 0) );
  ap_tran_y: assert property ( (state == YELLOW && count == 2 ) |=> (state == RED    && count == 0) );
  ap_tran_r: assert property ( (state == RED    && count == 10) |=> (state == GREEN  && count == 0) );

  // Minimal, meaningful coverage: observe each legal transition with counter reset
  cv_g2y: cover property ( state == GREEN  && count == 10 ##1 state == YELLOW && count == 0 );
  cv_y2r: cover property ( state == YELLOW && count == 2  ##1 state == RED    && count == 0 );
  cv_r2g: cover property ( state == RED    && count == 10 ##1 state == GREEN  && count == 0 );

  // Full cycle coverage (G->Y->R->G) with resets at each phase entry
  cv_full_cycle: cover property (
    state == GREEN && count == 0
    ##[1:$] state == YELLOW && count == 0
    ##[1:$] state == RED    && count == 0
    ##1      state == GREEN && count == 0
  );

endmodule

bind traffic_light_controller traffic_light_controller_sva sva_tlc ();

// Note: These assertions intentionally require the counter to reset to 0 on each state transition and enforce exact phase lengths (G=10, Y=2, R=10).