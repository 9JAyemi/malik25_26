// SVA for rgb_led
// Bind this module to the DUT: bind rgb_led rgb_led_sva #(.HZ_PER_COLOR_DIVISION(HZ_PER_COLOR_DIVISION), .PWM_PERIOD(PWM_PERIOD)) rgb_led_sva();

module rgb_led_sva #(parameter int HZ_PER_COLOR_DIVISION = 3921,
                     parameter int PWM_PERIOD = 1000000);

  // Use DUT scope signals directly (via bind)
  // Clocking
  default clocking cb @(posedge pclk); endclocking

  // -------------------------
  // Reset behavior (synchronous low)
  // -------------------------
  // Pending LED states cleared on reset
  assert property (@(posedge pclk) !nreset |-> (pending_led_state_1 == 32'h0 && pending_led_state_2 == 32'h0));
  // Internal states and PWMs cleared on reset
  assert property (@(posedge pclk) !nreset |-> (led_state_1 == 32'h0 && led_state_2 == 32'h0 &&
                                                pwm_r == 1'b0 && pwm_g == 1'b0 && pwm_b == 1'b0));

  // -------------------------
  // Bus protocol/checks
  // -------------------------
  // Read/write are mutually exclusive
  assert property (@(posedge pclk) disable iff (!nreset) !(bus_write_en && bus_read_en));

  // Writes update targeted registers on next cycle
  assert property (@(posedge pclk) disable iff (!nreset)
                   bus_write_en && (bus_addr[3:2] == 2'b00) |=> (led_control == $past(bus_write_data)));
  assert property (@(posedge pclk) disable iff (!nreset)
                   bus_write_en && (bus_addr[3:2] == 2'b01) |=> (pending_led_state_1 == $past(bus_write_data)));
  assert property (@(posedge pclk) disable iff (!nreset)
                   bus_write_en && (bus_addr[3:2] == 2'b10) |=> (pending_led_state_2 == $past(bus_write_data)));

  // Reads return the addressed register value on next cycle
  assert property (@(posedge pclk) disable iff (!nreset)
                   bus_read_en && (bus_addr[3:2] == 2'b00) |=> (bus_read_data == $past(led_control)));
  assert property (@(posedge pclk) disable iff (!nreset)
                   bus_read_en && (bus_addr[3:2] == 2'b01) |=> (bus_read_data == $past(pending_led_state_1)));
  assert property (@(posedge pclk) disable iff (!nreset)
                   bus_read_en && (bus_addr[3:2] == 2'b10) |=> (bus_read_data == $past(pending_led_state_2)));

  // -------------------------
  // Field extraction from current_state
  // Note: widths in RTL imply LSB of each slice is taken
  // -------------------------
  assert property (@(posedge pclk) disable iff (!nreset)
                   (enabled == current_state[31]) &&
                   (pulse   == current_state[24]) &&
                   (red     == current_state[16]) &&
                   (green   == current_state[8])  &&
                   (blue    == current_state[0]));

  // -------------------------
  // PWM counter behavior (increment and wrap)
  // -------------------------
  assert property (@(posedge pclk)
                   nreset && $past(nreset) |-> (
                     duty_cycle_counter ==
                       (($past(duty_cycle_counter) == PWM_PERIOD) ? 32'd0 : ($past(duty_cycle_counter) + 32'd1))
                   ));

  // -------------------------
  // State machine: toggling and updates at period boundary
  // -------------------------
  // current_state only changes on period boundary
  assert property (@(posedge pclk) disable iff (!nreset)
                   (duty_cycle_counter != 32'd0) |-> $stable(current_state));

  // On boundary (prev count == 0): toggle current_state between led_state_1/2
  assert property (@(posedge pclk) disable iff (!nreset)
                   $past(duty_cycle_counter) == 32'd0 |-> 
                     (current_state == (($past(current_state) == $past(led_state_1)) ? $past(led_state_2) : $past(led_state_1))));

  // On boundary, latch pending states into led_state_1/2
  assert property (@(posedge pclk) disable iff (!nreset)
                   $past(duty_cycle_counter) == 32'd0 |-> 
                     (led_state_1 == $past(pending_led_state_1) && led_state_2 == $past(pending_led_state_2)));

  // -------------------------
  // PWM behavior: turn-on at start of period, turn-off at programmed duty, stay low until next boundary
  // -------------------------
  // At the cycle after boundary (1 follows 0), PWMs were asserted high at the boundary edge
  assert property (@(posedge pclk) disable iff (!nreset)
                   (duty_cycle_counter == 32'd1 && $past(duty_cycle_counter) == 32'd0)
                   |-> ($past(pwm_r) && $past(pwm_g) && $past(pwm_b)));

  // Each color turns off exactly when its compare hits (if not at boundary), and stays low until next boundary
  assert property (@(posedge pclk) disable iff (!nreset)
                   (duty_cycle_counter != 32'd0) && ((red   * brightness_factor) == duty_cycle_counter)
                   |=> (pwm_r == 1'b0) until_with (duty_cycle_counter == 32'd0));
  assert property (@(posedge pclk) disable iff (!nreset)
                   (duty_cycle_counter != 32'd0) && ((green * brightness_factor) == duty_cycle_counter)
                   |=> (pwm_g == 1'b0) until_with (duty_cycle_counter == 32'd0));
  assert property (@(posedge pclk) disable iff (!nreset)
                   (duty_cycle_counter != 32'd0) && ((blue  * brightness_factor) == duty_cycle_counter)
                   |=> (pwm_b == 1'b0) until_with (duty_cycle_counter == 32'd0));

  // -------------------------
  // Coverage
  // -------------------------
  // Bus access coverage
  cover property (@(posedge pclk) disable iff (!nreset) bus_write_en && (bus_addr[3:2] == 2'b00));
  cover property (@(posedge pclk) disable iff (!nreset) bus_write_en && (bus_addr[3:2] == 2'b01));
  cover property (@(posedge pclk) disable iff (!nreset) bus_write_en && (bus_addr[3:2] == 2'b10));
  cover property (@(posedge pclk) disable iff (!nreset) bus_read_en  && (bus_addr[3:2] == 2'b00));
  cover property (@(posedge pclk) disable iff (!nreset) bus_read_en  && (bus_addr[3:2] == 2'b01));
  cover property (@(posedge pclk) disable iff (!nreset) bus_read_en  && (bus_addr[3:2] == 2'b10));

  // Counter wrap/period boundary
  cover property (@(posedge pclk) disable iff (!nreset)
                  (duty_cycle_counter == 32'd0) && $past(duty_cycle_counter) != 32'd0);

  // State toggle across two consecutive boundaries
  cover property (@(posedge pclk) disable iff (!nreset)
                  $past(duty_cycle_counter) == 32'd0 && (current_state == $past(led_state_2)));

  // PWM turn-off events seen for each color within a period
  cover property (@(posedge pclk) disable iff (!nreset)
                  (duty_cycle_counter != 32'd0) && ((red   * brightness_factor) == duty_cycle_counter));
  cover property (@(posedge pclk) disable iff (!nreset)
                  (duty_cycle_counter != 32'd0) && ((green * brightness_factor) == duty_cycle_counter));
  cover property (@(posedge pclk) disable iff (!nreset)
                  (duty_cycle_counter != 32'd0) && ((blue  * brightness_factor) == duty_cycle_counter));

  // Brightness range interest points (optional coverage)
  cover property (@(posedge pclk) disable iff (!nreset) brightness == 32'd0);
  cover property (@(posedge pclk) disable iff (!nreset) brightness == 32'd100000000);

endmodule