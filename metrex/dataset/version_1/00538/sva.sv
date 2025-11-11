// SVA for sonar_driver
// Bind as: bind sonar_driver sonar_driver_sva #(.freq(freq)) u_sva(.dut);
// Focused, concise checks + coverage.

module sonar_driver_sva #(parameter int freq = 50_000_000) (sonar_driver dut);

  // Use DUT-local params/states
  localparam int CYCLES_10_US = dut.CYCLES_10_US;
  localparam int ECHO_TIMEOUT = dut.ECHO_TIMEOUT;
  localparam int NM_PER_CYCLE = dut.NM_PER_CYCLE;

  default clocking cb @(posedge dut.clk); endclocking
  default disable iff (!dut.rst_n);

  // Basic sanity
  a_legal_state:        assert property (dut.state inside {dut.IDLE,dut.TRIG,dut.WAIT_ECHO,dut.MEASURING,dut.READY});
  a_state_follows_next: assert property (dut.rst_n && $past(dut.rst_n) |-> dut.state == $past(dut.next_state));
  a_distance_map:       assert property (dut.distance == dut.i_dist[31:24]);

  // Reset behavior (after deassert)
  a_after_reset: assert property ($rose(dut.rst_n) |-> dut.state==dut.IDLE && dut.ready && !dut.trig && dut.counter==0 && dut.i_dist==0);

  // IDLE accept measure, load counters, clear ready
  a_idle_measure_loads: assert property (dut.state==dut.IDLE && dut.measure |-> !dut.ready && dut.counter==CYCLES_10_US && dut.timeout==ECHO_TIMEOUT);
  a_idle_to_trig:       assert property (dut.state==dut.IDLE && dut.measure |=> dut.state==dut.TRIG);
  a_measure_while_busy: assert property ((dut.state!=dut.IDLE && dut.measure) |=> dut.state==$past(dut.state)); // ignored while busy
  a_idle_ready_high:    assert property (dut.state==dut.IDLE && !dut.measure |-> dut.ready);

  // TRIG pulse correctness
  a_trig_by_state:      assert property (dut.state==dut.TRIG |-> dut.trig);
  a_trig_low_else:      assert property (dut.state!=dut.TRIG |-> !dut.trig);
  a_trig_len_exact:     assert property ((dut.state==dut.IDLE && dut.measure)
                                         ##1 (dut.state==dut.TRIG && dut.trig)[*CYCLES_10_US]
                                         ##1 (dut.state==dut.WAIT_ECHO && !dut.trig));
  a_trig_counter_dec:   assert property (dut.state==dut.TRIG && $past(dut.state)==dut.TRIG && $past(dut.counter)>0
                                         |-> dut.counter == $past(dut.counter)-1);
  a_trig_exit_on_zero:  assert property (dut.state==dut.WAIT_ECHO && $past(dut.state)==dut.TRIG |-> $past(dut.counter)==0);
  a_i_dist_zero_in_trig:assert property (dut.state==dut.TRIG |-> dut.i_dist==0);

  // WAIT_ECHO behavior
  a_wait_trig_low:      assert property (dut.state==dut.WAIT_ECHO |-> !dut.trig);
  a_wait_timeout_dec:   assert property (dut.state==dut.WAIT_ECHO && $past(dut.state)==dut.WAIT_ECHO
                                         |-> dut.timeout == $past(dut.timeout)-1);
  a_wait_to_meas_on_echo:assert property (dut.state==dut.MEASURING && $past(dut.state)==dut.WAIT_ECHO |-> $past(dut.echo));
  a_wait_to_ready_on_to: assert property (dut.state==dut.READY && $past(dut.state)==dut.WAIT_ECHO |-> $past(dut.timeout)==0);

  // MEASURING behavior
  a_meas_timeout_dec:   assert property (dut.state==dut.MEASURING && $past(dut.state)==dut.MEASURING
                                         |-> dut.timeout == $past(dut.timeout)-1);
  a_meas_accumulates:   assert property (dut.state==dut.MEASURING && $past(dut.state)==dut.MEASURING
                                         |-> dut.i_dist == $past(dut.i_dist)+NM_PER_CYCLE);
  a_meas_to_ready:      assert property (dut.state==dut.READY && $past(dut.state)==dut.MEASURING
                                         |-> (!$past(dut.echo)) || ($past(dut.timeout)==0));

  // i_dist stability when not measuring
  a_dist_stable_wait:   assert property (dut.state==dut.WAIT_ECHO && $past(dut.state)==dut.WAIT_ECHO
                                         |-> dut.i_dist == $past(dut.i_dist));

  // READY and ready signal
  a_ready_high_in_READY:assert property (dut.state==dut.READY |-> dut.ready);
  a_ready_low_when_busy:assert property ((dut.state inside {dut.TRIG,dut.WAIT_ECHO,dut.MEASURING}) |-> !dut.ready);
  a_ready_to_idle:      assert property (dut.state==dut.READY |=> dut.state==dut.IDLE);

  // Coverage
  c_full_echo_path: cover property ((dut.state==dut.IDLE && dut.measure)
                                    ##1 (dut.state==dut.TRIG)[*CYCLES_10_US]
                                    ##1 dut.state==dut.WAIT_ECHO
                                    ##[1:$] dut.state==dut.MEASURING
                                    ##[1:$] (dut.state==dut.MEASURING && !dut.echo)
                                    ##1 dut.state==dut.READY ##1 dut.state==dut.IDLE);

  c_timeout_path:    cover property ((dut.state==dut.IDLE && dut.measure)
                                    ##1 (dut.state==dut.TRIG)[*CYCLES_10_US]
                                    ##1 dut.state==dut.WAIT_ECHO
                                    ##[1:$] (dut.state==dut.WAIT_ECHO && dut.timeout==0)
                                    ##1 dut.state==dut.READY);

  c_dist_changes:    cover property (dut.state==dut.MEASURING && $past(dut.state)==dut.MEASURING
                                    && dut.distance != $past(dut.distance));

  c_trig_width:      cover property ((dut.state==dut.IDLE && dut.measure)
                                    ##1 (dut.state==dut.TRIG && dut.trig)[*CYCLES_10_US]);

endmodule