// SVA for blinki. Bind into the DUT type.
// Focus: reset behavior, FSM correctness, timer semantics, LED behavior, and coverage.

module blinki_assertions
(
  input  logic        Reset_n_i,
  input  logic        Clk_i,
  input  logic        LED_o,
  input  logic [15:0] PeriodH_i,
  input  logic [15:0] PeriodL_i,
  input  logic [2:0]  State,
  input  logic [2:0]  NextState,
  input  logic        TimerPreset,
  input  logic        TimerEnable,
  input  logic        TimerOvfl,
  input  logic [31:0] Timer
);

  // Mirror FSM encodings
  localparam logic [2:0] stStart = 3'b000;
  localparam logic [2:0] stOn    = 3'b001;
  localparam logic [2:0] stOff   = 3'b010;

  // Basic sanity
  a_state_legal:       assert property (@(posedge Clk_i) State inside {stStart, stOn, stOff});
  a_no_x_state:        assert property (@(posedge Clk_i) !$isunknown(State));
  a_timerovfl_def:     assert property (@(posedge Clk_i) TimerOvfl == (Timer == 32'd0));
  a_timerenable_one:   assert property (@(posedge Clk_i) disable iff (!Reset_n_i) TimerEnable);

  // Reset behavior
  a_reset_hold:        assert property (@(posedge Clk_i) !Reset_n_i |-> (State==stStart && Timer==32'd0));
  a_reset_release:     assert property (@(posedge Clk_i) $rose(Reset_n_i) |=> (State==stOn && Timer=={PeriodH_i,PeriodL_i}));

  // NextState combinational correctness
  a_ns_start:          assert property (@(posedge Clk_i) disable iff (!Reset_n_i)
                                        (State==stStart) |-> (NextState==stOn && TimerPreset && TimerEnable));
  a_ns_on_ovfl:        assert property (@(posedge Clk_i) disable iff (!Reset_n_i)
                                        (State==stOn  && TimerOvfl)  |-> (NextState==stOff && TimerPreset));
  a_ns_on_hold:        assert property (@(posedge Clk_i) disable iff (!Reset_n_i)
                                        (State==stOn  && !TimerOvfl) |-> (NextState==stOn  && !TimerPreset));
  a_ns_off_ovfl:       assert property (@(posedge Clk_i) disable iff (!Reset_n_i)
                                        (State==stOff && TimerOvfl)  |-> (NextState==stOn  && TimerPreset));
  a_ns_off_hold:       assert property (@(posedge Clk_i) disable iff (!Reset_n_i)
                                        (State==stOff && !TimerOvfl) |-> (NextState==stOff && !TimerPreset));

  // State register should follow NextState
  a_state_follows_ns:  assert property (@(posedge Clk_i) disable iff (!Reset_n_i)
                                        State == $past(NextState));

  // Timer behavior: load and decrement
  a_timer_load:        assert property (@(posedge Clk_i) disable iff (!Reset_n_i)
                                        TimerPreset |=> (Timer == $past({PeriodH_i,PeriodL_i})));
  a_timer_dec:         assert property (@(posedge Clk_i) disable iff (!Reset_n_i)
                                        (!TimerPreset && TimerEnable) |=> (Timer == $past(Timer)-1));

  // LED correctness vs state
  a_led_on:            assert property (@(posedge Clk_i) disable iff (!Reset_n_i) (State==stOn)  |->  LED_o);
  a_led_off:           assert property (@(posedge Clk_i) disable iff (!Reset_n_i) (State==stOff) |-> !LED_o);
  a_led_change_with_state:
                        assert property (@(posedge Clk_i) disable iff (!Reset_n_i)
                                        $changed(LED_o) |-> $changed(State));

  // Functional coverage
  c_reset_to_on:       cover property (@(posedge Clk_i) $rose(Reset_n_i) ##1 (State==stOn));
  c_blink_cycle:       cover property (@(posedge Clk_i)
                                        (State==stOn) ##1 TimerOvfl ##1 (State==stOff) ##1 TimerOvfl ##1 (State==stOn));
  c_timer_load:        cover property (@(posedge Clk_i) disable iff (!Reset_n_i)
                                        TimerPreset ##1 (Timer == {PeriodH_i,PeriodL_i}));
  c_led_toggle:        cover property (@(posedge Clk_i) disable iff (!Reset_n_i) $changed(LED_o));

endmodule

bind blinki blinki_assertions ba (.*);