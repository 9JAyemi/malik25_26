// SVA for debouncer (bind into DUT). Focused, high-quality checks + coverage.
module debouncer_sva;
  // This module is meant to be bound into 'debouncer' and uses its internal signals.
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always_ff @(posedge clk) past_valid <= 1;
  default disable iff (!past_valid);

  // On input change: sample input and load counter to debounce_time
  assert property ( (signal_in != $past(signal_in_reg))
                    |=> (signal_in_reg == $past(signal_in) && debounce_counter == $past(debounce_time)) );

  // While stable and counter > 0: decrement by 1; no other state changes
  assert property ( (signal_in == $past(signal_in_reg) && $past(debounce_counter) > 0)
                    |=> (debounce_counter == $past(debounce_counter) - 1 &&
                         signal_in_reg   == $past(signal_in_reg) &&
                         signal_out      == $past(signal_out)) );

  // While stable and counter == 0: update output to input and reload counter
  assert property ( (signal_in == $past(signal_in_reg) && $past(debounce_counter) == 0)
                    |=> (signal_out      == $past(signal_in) &&
                         debounce_counter == $past(debounce_time) &&
                         signal_in_reg    == $past(signal_in_reg)) );

  // signal_in_reg may only change when input differs, and must take sampled input value
  assert property ( (signal_in_reg != $past(signal_in_reg))
                    |-> ($past(signal_in) != $past(signal_in_reg) && signal_in_reg == $past(signal_in)) );

  // Output can change only when prior cycle had counter==0 and no input change
  assert property ( (signal_out != $past(signal_out))
                    |-> ($past(debounce_counter) == 0 && $past(signal_in == signal_in_reg)) );

  // Basic functional coverage
  cover property ( signal_in != $past(signal_in_reg) ); // change detected / counter reload
  cover property ( signal_in == $past(signal_in_reg) && $past(debounce_counter) > 0 ); // counting down
  cover property ( signal_in == $past(signal_in_reg) && $past(debounce_counter) == 0 &&
                   signal_out == $past(signal_in) ); // output update event
  // Corner: zero debounce time -> output updates next cycle
  cover property ( (signal_in != $past(signal_in_reg) && $past(debounce_time) == 0)
                   ##1 (signal_out != $past(signal_out)) );
  // Non-zero debounce time -> output updates after >1 cycle
  cover property ( (signal_in != $past(signal_in_reg) && $past(debounce_time) > 1)
                   ##[2:$] (signal_out != $past(signal_out)) );
endmodule

bind debouncer debouncer_sva i_debouncer_sva();