// SVA for module: timer
// Bind-in assertions with full functional checks and compact coverage

`ifndef TIMER_SVA
`define TIMER_SVA

bind timer timer_sva t_sva();

module timer_sva (timer m);

  default clocking cb @ (posedge m.clk); endclocking

  // Reset effect (no disable iff)
  assert property (@(posedge m.clk)
                   m.reset |=> (m.timer==36'h0 && !m.timer_active && !m.timer_elapsed));

  // Increment while active (unless cleared that cycle)
  assert property (disable iff (m.reset)
                   (m.timer_active && !m.timer_elapsed && !(m.update_timers && m.fsm_clear_timer))
                   |=> m.timer == $past(m.timer)+1);

  // Elapse detection deactivates timer and sets elapsed
  assert property (disable iff (m.reset)
                   (m.timer_active && (m.timer >= m.timer_limit))
                   |=> (m.timer_elapsed && !m.timer_active));

  // Elapsed is sticky until clear
  assert property (disable iff (m.reset)
                   (m.timer_elapsed && !(m.update_timers && m.fsm_clear_timer))
                   |=> m.timer_elapsed);

  // Hold when inactive and not clearing
  assert property (disable iff (m.reset)
                   (!m.timer_active && !m.timer_elapsed && !(m.update_timers && m.fsm_clear_timer))
                   |=> (m.timer == $past(m.timer)));

  // While elapsed and inactive (and no start this cycle), timer remains 0
  assert property (disable iff (m.reset)
                   (m.timer_elapsed && !m.timer_active && !(m.update_timers && m.fsm_start_timer))
                   |=> (m.timer == 36'h0));

  // Start/stop semantics (stop wins over start)
  assert property (disable iff (m.reset)
                   (m.update_timers && m.fsm_stop_timer) |=> !m.timer_active);
  assert property (disable iff (m.reset)
                   (m.update_timers && m.fsm_start_timer && !m.fsm_stop_timer) |=> m.timer_active);

  // Clear semantics (no start/stop same cycle)
  assert property (disable iff (m.reset)
                   (m.update_timers && m.fsm_clear_timer && !(m.fsm_start_timer || m.fsm_stop_timer))
                   |=> (m.timer==36'h0 && !m.timer_elapsed && m.timer_active==$past(m.timer_active)));

  // Elapsed can only rise due to active compare
  assert property (disable iff (m.reset)
                   $rose(m.timer_elapsed) |-> $past(m.timer_active && (m.timer >= m.timer_limit)));

  // timer_limit writes (LSW/MSW) and hold when !wrenb
  assert property (disable iff (m.reset)
                   (m.wrenb && (m.wraddr==1'b0))
                   |=> (m.timer_limit[31:0]  == $past(m.config_data) &&
                        m.timer_limit[35:32] == $past(m.timer_limit[35:32])));
  assert property (disable iff (m.reset)
                   (m.wrenb && (m.wraddr==1'b1))
                   |=> (m.timer_limit[35:32] == $past(m.config_data[3:0]) &&
                        m.timer_limit[31:0]  == $past(m.timer_limit[31:0])));
  assert property (disable iff (m.reset)
                   (!m.wrenb) |=> $stable(m.timer_limit));

  // Coverage
  cover property (disable iff (m.reset)
                  (m.wrenb && m.wraddr==1'b0) ##1 (m.wrenb && m.wraddr==1'b1) ##1
                  (m.update_timers && m.fsm_start_timer) ##[1:$]
                  (m.timer_active && (m.timer >= m.timer_limit)) ##1 m.timer_elapsed);

  cover property (disable iff (m.reset)
                  (m.update_timers && m.fsm_start_timer) ##[1:10]
                  (m.update_timers && m.fsm_stop_timer && !m.timer_elapsed));

endmodule

`endif