// SVA for LCB
// Bindable, concise, focused on key behaviors and coverage

module LCB_sva
(
  input wire ain,
  input wire din,
  input wire aout,
  input wire dout,

  // internal DUT signals
  input wire [9:0] adc_out,
  input wire [3:0] debounce_counter,
  input wire       debounced_din,
  input wire       threshold,
  input wire       light_on,
  input wire [9:0] pwm_counter,
  input wire       pwm_out
);

  default clocking cb @ (posedge $global_clock); endclocking

  bit init;
  initial init = 1'b0;
  always @(posedge $global_clock) init <= 1'b1;
  default disable iff (!init);

  // ADC: update only on ain posedge; value becomes 1023
  assert property ($rose(ain) |-> ##0 adc_out == 10'd1023);
  assert property ($changed(adc_out) |-> $rose(ain));

  // Debounce: counter increments mod-16 on din posedge
  assert property ($rose(din) |-> ##0 debounce_counter == (($past(debounce_counter)+1) & 4'hF));
  assert property ($changed(debounce_counter) |-> $rose(din));

  // Debounced sample only on wrap; at din posedge it must capture 1
  assert property ($rose(din) && ($past(debounce_counter) != 4'hF) |-> ##0 $stable(debounced_din));
  assert property ($rose(din) && ($past(debounce_counter) == 4'hF) |-> ##0 debounced_din == 1'b1);
  assert property ($changed(debounced_din) |-> ($rose(din) && $past(debounce_counter)==4'hF));

  // Comparator: constant threshold intended at 512 and equivalence to compare
  assert property (threshold == 10'd512);
  assert property (light_on == (adc_out > 10'd512));
  assert property ($changed(light_on) |-> $changed(adc_out));

  // PWM: increment on light_on posedge; pwm_out computed from previous values
  assert property ($rose(light_on) |-> ##0 pwm_counter == (($past(pwm_counter)+1) & 10'h3FF));
  assert property ($changed(pwm_counter) |-> $rose(light_on));
  assert property ($rose(light_on) |-> ##0 pwm_out == ($past(pwm_counter) < (($past(adc_out)*9)/10)));
  assert property ($changed(pwm_out) |-> $rose(light_on));

  // Outputs wiring
  assert property (aout == pwm_out);
  assert property (dout == (light_on && debounced_din));

  // Coverage
  cover property ($rose(ain));
  cover property ($rose(din));
  cover property (adc_out <= 10'd512 && !light_on);
  cover property (adc_out >  10'd512 && light_on);
  cover property ($rose(din) && $past(debounce_counter)==4'hF ##0 debounced_din==1);
  cover property ($rose(light_on));
  cover property ($rose(light_on) && $past(pwm_counter)==10'h3FF ##0 pwm_counter==10'h000);
  cover property ($changed(pwm_out));
  cover property (dout);

endmodule

bind LCB LCB_sva lcb_sva_bind (
  .ain(ain),
  .din(din),
  .aout(aout),
  .dout(dout),
  .adc_out(adc_out),
  .debounce_counter(debounce_counter),
  .debounced_din(debounced_din),
  .threshold(threshold),
  .light_on(light_on),
  .pwm_counter(pwm_counter),
  .pwm_out(pwm_out)
);