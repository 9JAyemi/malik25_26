// SVA for thermal_management_block
// Bind-ready: uses internal regs via port connections

module thermal_management_block_sva (
  input  logic        clk,
  input  logic        rst,
  input  logic        temp_sensor,
  input  logic [7:0]  temp_threshold_high,
  input  logic [7:0]  temp_threshold_low,
  input  logic [7:0]  fan_speed,
  input  logic [7:0]  temp_digital,
  input  logic [7:0]  adc_value,
  input  logic [7:0]  filtered_value,
  input  logic [7:0]  pwm_count
);

  logic past_valid;
  always_ff @(posedge clk) begin
    if (rst) past_valid <= 1'b0;
    else     past_valid <= 1'b1;
  end

  // Reset values
  assert property (@(posedge clk)
    rst |-> (adc_value==8'h00 && filtered_value==8'h00 &&
             pwm_count==8'h00 && fan_speed==8'h00 && temp_digital==8'h00)
  );

  // ADC: sample and width behavior
  assert property (@(posedge clk) disable iff (rst || !past_valid)
    adc_value == $past(temp_sensor)
  );
  assert property (@(posedge clk) disable iff (rst)
    !$isunknown(adc_value) && (adc_value[7:1]==7'b0) // zero-extended 1-bit sensor
  );

  // Digital filter recurrence: uses previous-cycle values
  assert property (@(posedge clk) disable iff (rst || !past_valid)
    filtered_value == (($past(filtered_value) + $past(adc_value)) >> 1)
  );

  // Digital temperature output: one-cycle delayed filtered_value
  assert property (@(posedge clk) disable iff (rst || !past_valid)
    temp_digital == $past(filtered_value)
  );

  // PWM counter behavior
  assert property (@(posedge clk) disable iff (rst || !past_valid)
    ($past(pwm_count) <  $past(filtered_value)) |-> (pwm_count == $past(pwm_count)+8'h01)
  );
  assert property (@(posedge clk) disable iff (rst || !past_valid)
    ($past(pwm_count) >= $past(filtered_value)) |-> (pwm_count == 8'h00)
  );

  // Fan speed updates only on wrap, according to thresholds
  assert property (@(posedge clk) disable iff (rst || !past_valid)
    ($past(pwm_count) <  $past(filtered_value)) |-> (fan_speed == $past(fan_speed))
  );
  assert property (@(posedge clk) disable iff (rst || !past_valid)
    ($past(pwm_count) >= $past(filtered_value) &&
     ($past(filtered_value) > $past(temp_threshold_high))) |-> (fan_speed == 8'hFF)
  );
  assert property (@(posedge clk) disable iff (rst || !past_valid)
    ($past(pwm_count) >= $past(filtered_value) &&
     ($past(filtered_value) < $past(temp_threshold_low))) |-> (fan_speed == 8'h00)
  );
  assert property (@(posedge clk) disable iff (rst || !past_valid)
    ($past(pwm_count) >= $past(filtered_value) &&
     !($past(filtered_value) > $past(temp_threshold_high)) &&
     !($past(filtered_value) < $past(temp_threshold_low))) |-> (fan_speed == $past(fan_speed))
  );

  // No X/Z on key state when not in reset
  assert property (@(posedge clk) disable iff (rst)
    !$isunknown({fan_speed, temp_digital, filtered_value, pwm_count})
  );

  // Minimal functional coverage
  cover property (@(posedge clk) $fell(rst));
  cover property (@(posedge clk) past_valid &&
    ($past(pwm_count) <  $past(filtered_value)) && (pwm_count == $past(pwm_count)+1)
  );
  cover property (@(posedge clk) past_valid &&
    ($past(pwm_count) >= $past(filtered_value)) && (pwm_count == 8'h00)
  );
  cover property (@(posedge clk) past_valid &&
    ($past(pwm_count) >= $past(filtered_value)) && ($past(filtered_value) > $past(temp_threshold_high))
  );
  cover property (@(posedge clk) past_valid &&
    ($past(pwm_count) >= $past(filtered_value)) && ($past(filtered_value) < $past(temp_threshold_low))
  );
  cover property (@(posedge clk) past_valid &&
    ($past(pwm_count) >= $past(filtered_value)) &&
    !($past(filtered_value) > $past(temp_threshold_high)) &&
    !($past(filtered_value) < $past(temp_threshold_low))
  );

endmodule

// Bind example
bind thermal_management_block thermal_management_block_sva sva_i (
  .clk(clk),
  .rst(rst),
  .temp_sensor(temp_sensor),
  .temp_threshold_high(temp_threshold_high),
  .temp_threshold_low(temp_threshold_low),
  .fan_speed(fan_speed),
  .temp_digital(temp_digital),
  .adc_value(adc_value),
  .filtered_value(filtered_value),
  .pwm_count(pwm_count)
);