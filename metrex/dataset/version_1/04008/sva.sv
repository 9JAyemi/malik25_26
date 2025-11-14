// SVA binder for Mealy_FSM_ROM
module Mealy_FSM_ROM_sva;
  // Use DUT scope symbols directly (bind inserts this module into DUT scope)
  default clocking cb @(posedge clk); endclocking

  // Helper: canonical ROM index (int to avoid 2-state truncation)
  function automatic int idx_from(input logic [2:0] s, input logic xv);
    idx_from = ((s*2) + xv) % 12;
  endfunction

  // Basic sanity/range/known checks
  a_known_signals:    assert property (!$isunknown({clk,reset,x,state,nextState,count})); 
  a_state_range:      assert property (state     inside {[3'd0:3'd5]});
  a_nextState_range:  assert property (nextState inside {[3'd0:3'd5]});
  a_count_range:      assert property (count     inside {[3'd0:3'd7]});

  // While reset asserted, state must hold s1
  a_reset_level:      assert property (reset |-> state == 3'd1);

  // Sequential correctness: state must update per ROM(previous state,x)
  a_state_from_rom:   assert property (disable iff (reset)
                          state == ROM[idx_from($past(state), $past(x))][5:3]);

  // Mealy output correctness at clock sample: count matches ROM(previous state,x)
  a_count_from_rom:   assert property (disable iff (reset)
                          count == ROM[idx_from($past(state), $past(x))][2:0]);

  // Current-cycle combinational consistency: nextState/count pair matches ROM(current state,x)
  a_pair_consistent:  assert property (disable iff (reset)
                          {nextState, count} == ROM[idx_from(state, x)]);

  // Optional: state must equal previously computed nextState (detect missed comb/sensitivity issues)
  a_state_eq_past_next: assert property (disable iff (reset)
                              state == $past(nextState));

  // Coverage
  cover_reset:        cover property (@(posedge reset) 1);

  // Visit all 6 states
  genvar s;
  generate
    for (s=0; s<6; s++) begin : C_ST
      cover_state: cover property (disable iff (reset) state == s[2:0]);
    end
  endgenerate

  // Exercise both x values in each state
  generate
    for (s=0; s<6; s++) begin : C_STX
      cover_x0: cover property (disable iff (reset) (state == s[2:0]) && (x==1'b0));
      cover_x1: cover property (disable iff (reset) (state == s[2:0]) && (x==1'b1));
    end
  endgenerate

  // Hit all ROM entries used by the transition/output function
  genvar i;
  generate
    for (i=0; i<12; i++) begin : C_IDX
      cover_idx: cover property (disable iff (reset)
                      idx_from($past(state), $past(x)) == i);
    end
  endgenerate
endmodule

bind Mealy_FSM_ROM Mealy_FSM_ROM_sva sva_mealy_rom();