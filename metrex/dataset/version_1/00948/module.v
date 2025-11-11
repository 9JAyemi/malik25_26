module thermal_management_block (
  input clk,
  input rst,
  input temp_sensor,
  input [7:0] temp_threshold_high,
  input [7:0] temp_threshold_low,
  output reg [7:0] fan_speed,
  output reg [7:0] temp_digital
);

  // ADC module
  reg [7:0] adc_value;
  always @(posedge clk) begin
    if (rst) begin
      adc_value <= 8'h00;
    end else begin
      adc_value <= temp_sensor;
    end
  end
  
  // Digital filter module
  reg [7:0] filtered_value;
  always @(posedge clk) begin
    if (rst) begin
      filtered_value <= 8'h00;
    end else begin
      filtered_value <= (filtered_value + adc_value) >> 1;
    end
  end
  
  // PWM module
  reg [7:0] pwm_count;
  always @(posedge clk) begin
    if (rst) begin
      pwm_count <= 8'h00;
      fan_speed <= 8'h00;
    end else begin
      if (pwm_count >= filtered_value) begin
        pwm_count <= 8'h00;
        if (filtered_value > temp_threshold_high) begin
          fan_speed <= 8'hFF;
        end else if (filtered_value < temp_threshold_low) begin
          fan_speed <= 8'h00;
        end
      end else begin
        pwm_count <= pwm_count + 1;
      end
    end
  end
  
  // Output digital temperature value
  always @(posedge clk) begin
    if (rst) begin
      temp_digital <= 8'h00;
    end else begin
      temp_digital <= filtered_value;
    end
  end
  
endmodule
