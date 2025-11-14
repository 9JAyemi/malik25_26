// SVA for light_up and led_flasher
// Bind into DUTs; concise but checks key behavior and provides useful coverage.

bind light_up light_up_sva u_light_up_sva();
module light_up_sva;

  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  // Header decode correctness
  assert property (correct_header == ((header==CORRECT_HEAD1)||(header==CORRECT_HEAD2)));

  // No state changes without a correct header
  assert property (disable iff (!past_valid)
                   !correct_header |-> (tachy_flash==$past(tachy_flash) &&
                                        brady_flash==$past(brady_flash) &&
                                        counter_previous==$past(counter_previous)));

  // On correct header: flashes reflect prior-cycle classification; counter_previous captures counter
  assert property (disable iff (!past_valid)
                   correct_header |-> (tachy_flash==$past(too_fast) &&
                                       brady_flash==$past(too_slow) &&
                                       counter_previous==$past(counter)));

  // After an update, difference uses the new counter_previous
  assert property (disable iff (!past_valid)
                   $past(correct_header) |-> (difference == (counter - $past(counter))));

  // Classification and stored flashes are mutually exclusive
  assert property (!(too_fast && too_slow));
  assert property (!(tachy_flash && brady_flash));

  // Gating: these can only change when header is correct
  assert property (disable iff (!past_valid) $changed(tachy_flash)      |-> correct_header);
  assert property (disable iff (!past_valid) $changed(brady_flash)       |-> correct_header);
  assert property (disable iff (!past_valid) $changed(counter_previous)  |-> correct_header);

  // Normal pin strictly reflects internal flashes
  assert property (normal_pin == (!tachy_flash && !brady_flash));

  // Functional coverage
  cover property (disable iff (!past_valid) correct_header && $past(too_fast));
  cover property (disable iff (!past_valid) correct_header && $past(too_slow));
  cover property (disable iff (!past_valid) correct_header && !$past(too_fast) && !$past(too_slow));
  cover property (normal_pin);

endmodule


bind led_flasher led_flasher_sva u_led_flasher_sva();
module led_flasher_sva;

  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  // Immediate drop when flash deasserts (counter reset -> LED_out low same cycle)
  assert property (!LED_flash |-> !LED_out);

  // After 8 consecutive high cycles of LED_flash, LED_out must be 1
  assert property (LED_flash[*8] |-> LED_out);

  // While LED_flash remains high, once LED_out=1 it stays 1
  assert property (disable iff (!past_valid)
                   LED_out && LED_flash && $past(LED_flash) |-> LED_out);

  // Functional coverage
  cover property (LED_flash[*8] ##1 LED_out);
  cover property ($fell(LED_flash) && !LED_out);

endmodule