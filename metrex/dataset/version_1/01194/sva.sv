// SVA for delay_gate
// Focus: correctness of counter, buffer updates, output mapping, and end-to-end delay spec.
// Bind these assertions to the DUT to access internal signals.

`ifndef DELAY_GATE_SVA
`define DELAY_GATE_SVA

// synthesis translate_off

module delay_gate_sva #(
  parameter int DELAY = 1
) (
  input  logic                         clk,
  input  logic                         data,
  input  logic                         delayed_data,
  input  logic [DELAY-1:0]             data_buffer,
  input  logic [DELAY-1:0]             delayed_data_buffer,
  input  logic [DELAY-1:0]             delay_counter
);

  // Elaboration-time sanity
  initial begin
    if (DELAY < 1) $error("delay_gate: DELAY must be >= 1");
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff ($initstate)

  // Counter must increment by 1 every cycle (modulo width)
  assert property (delay_counter == $past(delay_counter) + 1)
    else $error("delay_counter does not increment by 1");

  // data_buffer captures input data each cycle
  assert property (data_buffer == $past(data))
    else $error("data_buffer did not capture input data");

  // delayed_data_buffer updates only when gating condition true, else holds
  assert property ( ($past(delay_counter) == DELAY) |-> (delayed_data_buffer == $past(data_buffer)) )
    else $error("delayed_data_buffer not updated from data_buffer when expected");

  assert property ( ($past(delay_counter) != DELAY) |-> (delayed_data_buffer == $past(delayed_data_buffer)) )
    else $error("delayed_data_buffer changed unexpectedly");

  // Output mapping must reflect MSB of delayed_data_buffer
  assert property (delayed_data === delayed_data_buffer[DELAY-1])
    else $error("Output does not reflect delayed_data_buffer[MSB]");

  // End-to-end functional intent: output equals input delayed by DELAY cycles
  // This will flag design bugs (e.g., lack of shift and off-by-one issues).
  sequence hist_filled; 1[*DELAY]; endsequence
  assert property (hist_filled |-> (delayed_data == $past(data, DELAY)))
    else $error("Functional delay mismatch: delayed_data != $past(data, DELAY)");

  // X-propagation: after first update event, output should be known
  sequence first_update; $past(delay_counter) == DELAY; endsequence
  assert property (first_update |=> !$isunknown(delayed_data))
    else $error("delayed_data is X after an update event");

  // Coverage
  cover property (delay_counter == DELAY);                            // see a gating event
  cover property ($rose(data));                                       // data rises at least once
  cover property ($fell(data));                                       // data falls at least once
  cover property (hist_filled ##1 (delayed_data == $past(data, DELAY))); // spec observed at least once
  cover property ($changed(delayed_data));                            // output toggles at least once

endmodule

// Bind into DUT to access internals
bind delay_gate delay_gate_sva #(.DELAY(DELAY)) delay_gate_sva_i (
  .clk                (clk),
  .data               (data),
  .delayed_data       (delayed_data),
  .data_buffer        (data_buffer),
  .delayed_data_buffer(delayed_data_buffer),
  .delay_counter      (delay_counter)
);

// synthesis translate_on

`endif