module Debouncer(
  input clk, // clock signal
  input rst_n, // asynchronous reset
  input in, // input signal
  output reg out // output signal
);

parameter COUNT_MAX = 1000; // maximum count value
parameter WAIT_TIME = 10; // wait time in ms

reg [9:0] count; // counter to count up to COUNT_MAX
reg [1:0] state; // state machine to control the debouncing process

always @(posedge clk or negedge rst_n) begin
  if (~rst_n) begin
    count <= 0;
    state <= 2'b00;
    out <= 1'b0;
  end
  else begin
    case (state)
      2'b00: // idle state
        if (in != out) begin
          count <= 0;
          state <= 2'b01;
        end
        else begin
          out <= in;
        end
      2'b01: // waiting state
        if (count >= COUNT_MAX) begin
          out <= in;
          state <= 2'b10;
        end
        else begin
          count <= count + 1;
        end
      2'b10: // debounce state
        if (in != out) begin
          count <= 0;
          state <= 2'b01;
        end
        else begin
          state <= 2'b00;
        end
    endcase
  end
end

endmodule