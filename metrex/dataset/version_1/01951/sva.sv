// SVA for debounce. Bind into the DUT to access internals.
module debounce_sva #(parameter int THRESH = 16'd10000)
(
  input clk,
  input button,
  input button_state,
  input button_up,
  input button_down,
  input current_state,
  input previous_state,
  input [15:0] debounce_counter
);

  default clocking cb @(posedge clk); endclocking
  default disable iff ($initstate);

  // Counter behavior
  // Monotonic +1 until THRESH, then saturates at THRESH
  assert property (debounce_counter < THRESH |=> debounce_counter == $past(debounce_counter)+1);
  assert property (debounce_counter >= THRESH |=> debounce_counter == THRESH);

  // Sampling relationships
  assert property (current_state  == $past(button));
  assert property (previous_state == $past(current_state));

  // Button state update policy
  assert property (debounce_counter < THRESH |-> $stable(button_state));
  assert property (debounce_counter == THRESH |-> button_state == current_state);
  assert property ($changed(button_state) |-> debounce_counter == THRESH);

  // Up/Down flag correctness and stickiness
  assert property ((debounce_counter == THRESH &&  current_state && !previous_state) |-> button_down);
  assert property ((debounce_counter == THRESH && !current_state &&  previous_state) |-> button_up);

  assert property ($rose(button_down) |-> (debounce_counter == THRESH &&  current_state && !previous_state));
  assert property ($rose(button_up)   |-> (debounce_counter == THRESH && !current_state &&  previous_state));

  assert property (!$fell(button_down));
  assert property (!$fell(button_up));

  // No early flags before threshold
  assert property (debounce_counter < THRESH |-> !button_up && !button_down);

  // Coverage
  cover property (debounce_counter == THRESH);
  cover property (debounce_counter == THRESH &&  current_state && !previous_state && button_down && button_state==current_state);
  cover property (debounce_counter == THRESH && !current_state &&  previous_state && button_up   && button_state==current_state);

endmodule

bind debounce debounce_sva #(.THRESH(16'd10000)) u_debounce_sva (.*);