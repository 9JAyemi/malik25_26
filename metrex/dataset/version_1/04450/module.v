module pulse_generator (
  input clk,
  input reset,
  input start,
  output reg pulse
);

  parameter PULSE_DURATION = 100; // in clock cycles
  parameter CLOCK_FREQUENCY = 50; // in MHz

  localparam PULSE_CYCLES = PULSE_DURATION * CLOCK_FREQUENCY;

  reg [31:0] count = 0;
  reg pulse_on = 0;

  always @(posedge clk) begin
    if (reset) begin
      count <= 0;
      pulse_on <= 0;
      pulse <= 0;
    end
    else begin
      if (start) begin
        count <= 0;
        pulse_on <= 1;
        pulse <= 1;
      end
      else begin
        if (count >= PULSE_CYCLES) begin
          pulse_on <= 0;
          pulse <= 0;
        end
        else begin
          count <= count + 1;
          pulse_on <= 1;
          pulse <= 1;
        end
      end
    end
  end

endmodule