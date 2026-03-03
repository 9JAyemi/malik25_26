// SVA for debounce: concise, high-quality checks and coverage
module debounce_sva (
  input logic        clk,
  input logic        PB,
  input logic        PB_state,
  input logic        init_state,
  input logic [11:0] PB_cnt,
  input logic        PB_cnt_max,
  input logic        PB_idle
);
  default clocking cb @(posedge clk); endclocking

  // Guard $past and initial Xs
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Sanity/definitions
  a_known:              assert property (!$isunknown({PB, PB_state, init_state, PB_cnt}));
  a_cnt_max_def:        assert property (PB_cnt_max == (&PB_cnt));
  a_idle_def:           assert property (PB_idle    == (PB_cnt == 12'd0));

  // Start of debounce window
  a_start:              assert property (PB_idle && (PB != init_state)
                                         |=> PB_cnt == 12'd1
                                             && init_state == $past(PB)
                                             && $stable(PB_state));

  // Idle hold (no change -> stay idle, nothing updates)
  a_idle_hold:          assert property (PB_idle && (PB == init_state)
                                         |=> PB_cnt == 12'd0
                                             && $stable(init_state)
                                             && $stable(PB_state));

  // Monotonic count while active (non-idle, not max)
  a_cnt_incr:           assert property ((PB_cnt != 12'd0) && !PB_cnt_max
                                         |=> PB_cnt == $past(PB_cnt) + 12'd1);

  // Commit at max: output updates, counter clears
  a_commit:             assert property (PB_cnt_max
                                         |=> PB_cnt == 12'd0
                                             && PB_state == $past(init_state));

  // Output changes only on commit
  a_state_change_only:  assert property ($changed(PB_state) |-> $past(PB_cnt_max));

  // While counting, captured init_state must not change
  a_init_stable:        assert property ((PB_cnt != 12'd0) |=> $stable(init_state));

  // While counting but not at max, output must not change
  a_state_stable_while_cnt: assert property ((PB_cnt != 12'd0) && !PB_cnt_max |=> $stable(PB_state));

  // The only way to return to idle from non-idle is via max commit
  a_only_reset_from_max: assert property (($past(PB_cnt) != 12'd0) && (PB_cnt == 12'd0)
                                          |-> $past(PB_cnt_max));

  // ------------- Coverage -------------

  // Full debounce cycle: detect change -> count -> commit -> clear
  c_full_cycle: cover property (PB_idle && (PB != init_state)
                                ##1 (PB_cnt == 12'd1)
                                ##[1:$] PB_cnt_max
                                ##1 (PB_cnt == 12'd0 && PB_state == init_state));

  // Bounce during counting is ignored, still commits to captured init_state
  c_bounce_ignored: cover property (PB_idle && (PB != init_state)
                                    ##1 (PB_cnt == 12'd1)
                                    ##[1:$] ((PB_cnt != 12'd0) && !PB_cnt_max && $changed(PB))
                                    ##[1:$] PB_cnt_max
                                    ##1 (PB_state == init_state));

  // Both directions observed
  c_0_to_1: cover property ((init_state == 1'b0) && (PB == 1'b1) && PB_idle
                            ##1 (PB_cnt == 12'd1)
                            ##[1:$] PB_cnt_max
                            ##1 (PB_state == 1'b1));

  c_1_to_0: cover property ((init_state == 1'b1) && (PB == 1'b0) && PB_idle
                            ##1 (PB_cnt == 12'd1)
                            ##[1:$] PB_cnt_max
                            ##1 (PB_state == 1'b0));
endmodule

// Bind to DUT (accessing internal signals)
bind debounce debounce_sva bdeb_sva (
  .clk(clk),
  .PB(PB),
  .PB_state(PB_state),
  .init_state(init_state),
  .PB_cnt(PB_cnt),
  .PB_cnt_max(PB_cnt_max),
  .PB_idle(PB_idle)
);