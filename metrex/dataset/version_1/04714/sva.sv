// SVA for Debouncer
// Note: design is clocked by button; all assertions use posedge button.

module Debouncer_sva #(
  parameter int clk_period    = 10,
  parameter int debounce_time = 50
) (
  input  logic       button,
  input  logic       debounced_signal,
  input  logic       button_state,
  input  logic [3:0] debounce_counter
);
  localparam int N = debounce_time/clk_period;
  localparam int W = $bits(debounce_counter);

  // Static/elaboration checks
  initial begin
    assert (N > 0) else $error("N=debounce_time/clk_period must be > 0");
    assert (N < (1<<W)) else $error("debounce_counter width (%0d) too small for N=%0d", W, N);
  end

  default clocking cb @(posedge button); endclocking

  // X/Z checks at sampling points
  ap_no_xz: assert property ( !$isunknown({button,debounced_signal,button_state,debounce_counter}) );

  // Counter always in 0..N
  ap_cnt_range: assert property ( debounce_counter inside {[0:N]} );

  // Load N when button differs from previous button_state
  ap_load_on_mismatch: assert property (
    disable iff ($isunknown({button_state,debounce_counter}))
    (button != $past(button_state)) |-> debounce_counter == N
  );

  // Decrement when equal and counter > 0
  ap_dec_when_equal: assert property (
    disable iff ($isunknown({button_state,debounce_counter}))
    (button == $past(button_state) && $past(debounce_counter) > 0)
      |-> debounce_counter == $past(debounce_counter) - 1
  );

  // At equality with counter == 0, button_state must remain stable and equal to button
  ap_state_stable_at_zero: assert property (
    disable iff ($isunknown({button_state,debounce_counter}))
    (button == $past(button_state) && $past(debounce_counter) == 0)
      |-> $stable(button_state) && (button_state == $past(button_state))
  );

  // debounced_signal updates only when prior counter == 0
  ap_debounced_updates_only_on_zero: assert property (
    disable iff ($isunknown(debounce_counter))
    $changed(debounced_signal) |-> $past(debounce_counter) == 0
  );

  // When prior counter == 0, debounced_signal equals prior button_state
  ap_debounced_eq_state: assert property (
    disable iff ($isunknown({button_state,debounce_counter}))
    ($past(debounce_counter) == 0) |-> (debounced_signal == $past(button_state))
  );

  // debounced_signal does not change while counter > 0
  ap_no_debounced_change_when_cnt_nonzero: assert property (
    disable iff ($isunknown(debounce_counter))
    $past(debounce_counter) > 0 |-> $stable(debounced_signal)
  );

  // Counter step legality: hold, load N on mismatch, or decrement by 1 when equal
  ap_cnt_step_legal: assert property (
    disable iff ($isunknown({button_state,debounce_counter}))
    1 |-> (debounce_counter == $past(debounce_counter)) ||
          ((button != $past(button_state)) && (debounce_counter == N)) ||
          ((button == $past(button_state)) && ($past(debounce_counter) > 0) &&
           (debounce_counter == $past(debounce_counter)-1))
  );

  // Coverage
  cv_load:       cover property (button != $past(button_state));
  cv_decrement:  cover property ((button == $past(button_state) && $past(debounce_counter) > 0)
                                 ##1 (debounce_counter == $past(debounce_counter)-1));
  cv_zero_update: cover property ($past(debounce_counter) == 0 ##1 $changed(debounced_signal));

endmodule

bind Debouncer Debouncer_sva #(.clk_period(clk_period), .debounce_time(debounce_time))
  debouncer_sva_i (
    .button(button),
    .debounced_signal(debounced_signal),
    .button_state(button_state),
    .debounce_counter(debounce_counter)
  );