// SVA for assert_unchange_assert
// Concise, high-value checks + key coverpoints
// Bind into the DUT so we can see internal regs

bind assert_unchange_assert assert_unchange_assert_sva ();

module assert_unchange_assert_sva;

  // Assume we are bound inside assert_unchange_assert scope
  // Ports/regs referenced directly

  // Default clock/reset
  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n);

  // Helper sequences/expressions
  function automatic bit changed_stable_chk;
    // Detect 4-state change the DUT is checking (test_expr !== prev_test_expr)
    // In the DUT's mid-window logic, prev_test_expr holds $past(test_expr)
    changed_stable_chk = (test_expr !== $past(test_expr));
  endfunction

  // In-DUT “mid-window” update points (three branches unify here)
  sequence mid_window_cycle;
    start_detected && ((window_counter < window) || (window_counter == window) || ignore_new_start);
  endsequence

  // 1) Reset behavior (async low, sync sampled)
  a_reset_clears: assert property (
    !reset_n |=> ($isunknown(prev_test_expr) && (window_counter==0) && !start_detected && !reset_detected && !pass && !fail && !error)
  );

  // 2) Start when idle initializes state
  a_start_idle_init: assert property (
    start_event && !start_detected |=> (prev_test_expr == $past(test_expr)) && (window_counter==1) && start_detected && !reset_detected && !pass && !fail && !error
  );

  // 3) Mid-window fail/error computation matches DUT spec
  a_midwin_flags: assert property (
    mid_window_cycle |=> (fail == (changed_stable_chk && xzcheck_enable)) && (error == (changed_stable_chk && xzcheck_enable))
  );

  // 4) Mid-window prev_test_expr always updates to current test_expr
  a_midwin_prev_updates: assert property (
    mid_window_cycle |=> (prev_test_expr == $past(test_expr))
  );

  // 5) Mid-window pass pulse at boundary, rollover and sticky start per ignore_new_start
  a_pass_and_rollover: assert property (
    start_detected && (window_counter == window) |=> pass && (window_counter==0) && (start_detected == $past(ignore_new_start))
  );

  // 6) Pass only asserted at a boundary
  a_pass_only_at_boundary: assert property (
    pass |-> $past(start_detected && (window_counter == window))
  );

  // 7) Non-boundary mid-window cycles do not assert pass
  a_no_pass_midwin_incr: assert property (
    start_detected && ((window_counter < window) || ignore_new_start) && !(window_counter == window) |=> !pass
  );

  // 8) Counter increments in mid-window non-boundary cycles
  a_counter_inc: assert property (
    start_detected && ((window_counter < window) || ignore_new_start) && !(window_counter == window) |=> (window_counter == $past(window_counter)+1)
  );

  // 9) xzcheck_enable=0 masks fail/error in mid-window
  a_mask_flags_when_disabled: assert property (
    mid_window_cycle && !xzcheck_enable |=> (!fail && !error)
  );

  // 10) Fail always implies error (anywhere)
  a_fail_implies_error: assert property ( fail |-> error );

  // 11) start_event while active with reset_on_new_start takes precedence; optional error
  a_restart_on_new_start_with_event: assert property (
    start_event && start_detected && reset_on_new_start |=> (prev_test_expr == $past(test_expr)) && (window_counter==1) && start_detected && !reset_detected && !pass && !fail && (error == $past(error_on_new_start))
  );

  // 12) start_event while active with error_on_new_start only (no reset_on_new_start) triggers immediate error/abort
  a_error_on_new_start_with_event_only: assert property (
    start_event && start_detected && !reset_on_new_start && error_on_new_start |=> error && !start_detected && (window_counter==0) && $isunknown(prev_test_expr) && !pass && !fail
  );

  // 13) reset_on_new_start without start_event sets reset_detected, and next cycle performs full reset
  a_reset_detected_two_cycle_clear: assert property (
    start_detected && reset_on_new_start && !start_event |=> reset_detected ##1 ($isunknown(prev_test_expr) && (window_counter==0) && !start_detected && !reset_detected && !pass && !fail && !error)
  );

  // 14) Late error_on_new_start without start_event (when not in any mid-window branch) aborts
  // This can occur if counter drifted past window when ignore_new_start previously held
  a_error_no_event_abort: assert property (
    start_detected && error_on_new_start &&
    !(window_counter < window) && !(window_counter == window) &&
    !ignore_new_start && !reset_on_new_start && !start_event
    |=> error && !start_detected && (window_counter==0) && $isunknown(prev_test_expr) && !pass && !fail
  );

  // 15) After any reset (hw or reset_detected handling), outputs flags are cleared
  a_reset_detected_clears_flags: assert property (
    $rose(reset_detected) |=> (!pass && !fail && !error)
  );

  // ----------------
  // Key functional coverpoints
  // ----------------

  // C1: Clean pass with stable test_expr
  c_pass: cover property (
    start_event && !start_detected ##1
    (!changed_stable_chk)[*1:$] ##1
    (start_detected && (window_counter == window)) ##1 pass
  );

  // C2: Change in window triggers fail/error
  c_fail_on_change: cover property (
    start_event && !start_detected ##1
    mid_window_cycle && changed_stable_chk && xzcheck_enable ##1 (fail && error)
  );

  // C3: Restart on new start with error_on_new_start set (precedence path)
  c_restart_with_error_flag: cover property (
    start_event && !start_detected ##1
    start_event && start_detected && reset_on_new_start && error_on_new_start ##1
    (start_detected && error)
  );

  // C4: reset_on_new_start without start_event causes reset_detected then full clear
  c_reset_detected_flow: cover property (
    start_event && !start_detected ##1
    start_detected && reset_on_new_start && !start_event ##1
    reset_detected ##1
    (!start_detected && !pass && !fail && !error)
  );

endmodule