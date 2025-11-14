// Bind these SVA to the DUT
bind ctr_fsm ctr_fsm_sva svainst();

module ctr_fsm_sva;
  // Using DUT scope signals/params directly via bind
  default clocking cb @(posedge clk); endclocking
  default disable iff (!ar) // active-low async reset

  // Invariants and decodes
  a_state_legal:   assert property (state inside {IDLE, PRERUN, RUN, STOPPED});
  a_out_ctr_en:    assert property (ctr_en == (state==RUN));
  a_out_ctr_ar:    assert property (ctr_ar == ~((state==PRERUN) || (state==IDLE)));
  a_no_x:          assert property (!$isunknown({state, ctr_en, ctr_ar}));

  // Reset behavior
  a_async_reset_holds_idle: assert property (!ar |-> state==IDLE);
  a_after_reset_idle:       assert property ($rose(ar) |=> state==IDLE);

  // Next-state function (per-state, per-input)
  a_idle_start:      assert property (state==IDLE   && start==start_assert     |=> state==PRERUN);
  a_idle_no_start:   assert property (state==IDLE   && start!=start_assert     |=> state==IDLE);

  a_prerun_stop:     assert property (state==PRERUN && stop==stop_assert       |=> state==STOPPED);
  a_prerun_no_stop:  assert property (state==PRERUN && stop!=stop_assert       |=> state==RUN);

  a_run_stop:        assert property (state==RUN    && stop==stop_assert       |=> state==STOPPED);
  a_run_no_stop:     assert property (state==RUN    && stop!=stop_assert       |=> state==RUN);

  a_stopped_to_idle: assert property (state==STOPPED&& start==~start_assert    |=> state==IDLE);
  a_stopped_hold:    assert property (state==STOPPED&& start!=~start_assert    |=> state==STOPPED);

  // Coverage
  c_state_idle:     cover property (state==IDLE);
  c_state_prerun:   cover property (state==PRERUN);
  c_state_run:      cover property (state==RUN);
  c_state_stopped:  cover property (state==STOPPED);

  // Happy path: IDLE -> PRERUN -> RUN -> STOPPED -> IDLE
  c_path_happy: cover property (
      state==IDLE   && start==start_assert ##1
      state==PRERUN && stop!=stop_assert   ##1
      state==RUN    && stop==stop_assert   ##1
      state==STOPPED&& start==~start_assert##1
      state==IDLE
  );

  // Abort in PRERUN
  c_prerun_abort: cover property (
      state==IDLE && start==start_assert ##1
      state==PRERUN && stop==stop_assert ##1
      state==STOPPED
  );

  // RUN hold and ctr_en toggle sequence
  c_run_hold:   cover property (state==RUN ##1 (stop!=stop_assert)[*2] ##1 state==RUN);
  c_en_toggle:  cover property (state==PRERUN ##1 state==RUN ##1 state==STOPPED);
endmodule