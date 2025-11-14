
module trafficLightController (
  input clk,
  input [1:0] currentState,
  output reg [1:0] nextState
);

// Power-on reset
initial begin
  nextState <= 2'b00; // Red state
end

// Define state transitions
always @(posedge clk) begin
  case (currentState)
    2'b00: // Red state
      if (count == 10) begin
        nextState <= 2'b10; // Green state
        count <= 0;
      end else begin
        count <= count + 1;
      end
    2'b10: // Green state
      if (count == 5) begin
        nextState <= 2'b01; // Yellow state
        count <= 0;
      end else begin
        count <= count + 1;
      end
    2'b01: // Yellow state
      if (count == 2) begin
        nextState <= 2'b00; // Red state
        count <= 0;
      end else begin
        count <= count + 1;
      end
    default: nextState <= 2'b00; // Red state
  endcase
end

reg [2:0] count;
parameter CLK_PERIOD = 10; // Clock period in ns
reg clk_internal;
always #CLK_PERIOD clk_internal = ~clk_internal; // Toggle clock signal

assign clk = clk_internal;

endmodule
