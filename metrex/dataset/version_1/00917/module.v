
module DLL (
  input clk,
  input rst,
  input in,
  output reg out
);

parameter delay_time = 10; // delay time in clock cycles

reg [delay_time-1:0] delay_line; // delay line implemented as a shift register
reg [1:0] phase_detector_out; // output of the phase detector
reg [delay_time-1:0] delay_time_reg; // register to hold the current delay time

always @(posedge clk) begin
  if (rst) begin
    delay_line <= 0;
    phase_detector_out <= 0;
    delay_time_reg <= delay_time;
  end else begin
    // shift the input signal into the delay line
    delay_line <= {in, delay_line[delay_time-1:1]};
    
    // compare the delayed signal to the input signal
    phase_detector_out <= {delay_line[delay_time-1], delay_line[delay_time-2]} ^ {in, delay_line[delay_time-1]};
    
    // adjust the delay time based on the phase detector output
    if (phase_detector_out == 2'b01) begin
      delay_time_reg <= delay_time_reg + 1;
    end else if (phase_detector_out == 2'b10) begin
      delay_time_reg <= delay_time_reg - 1;
    end
    
    // output the synchronized signal
    out <= delay_line[delay_time_reg-1];
  end
end

endmodule
