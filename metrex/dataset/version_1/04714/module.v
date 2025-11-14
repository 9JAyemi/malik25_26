
module Debouncer (
  input button,
  output reg debounced_signal
);

parameter clk_period = 10; // period of the clock signal in nanoseconds
parameter debounce_time = 50; // debounce time in nanoseconds

reg button_state;
reg [3:0] debounce_counter;

always @(posedge button) begin
  if (button != button_state) begin
    debounce_counter <= debounce_time / clk_period;
  end else if (debounce_counter > 0) begin
    debounce_counter <= debounce_counter - 1;
  end else begin
    button_state <= button;
  end
end

always @(posedge button) begin
  if (debounce_counter == 0) begin
    debounced_signal <= button_state;
  end
end

endmodule