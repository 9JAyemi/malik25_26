module pwm (
  input clk,
  input ctrl,
  output reg pwm
);

  reg [7:0] duty_cycle = 8'h80; // initialize duty cycle to 50%
  reg [7:0] counter = 8'h00; // initialize counter to 0
  
  always @(posedge clk) begin
    if (counter == 8'hFF) begin
      counter <= 8'h00;
    end else begin
      counter <= counter + 1;
    end
    
    if (counter < duty_cycle) begin
      pwm <= 1;
    end else begin
      pwm <= 0;
    end
  end
  
  always @(posedge clk) begin
    if (ctrl > 8'hFF) begin
      duty_cycle <= 8'hFF;
    end else begin
      duty_cycle <= ctrl;
    end
  end
  
endmodule