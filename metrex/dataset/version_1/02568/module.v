
module touch_sensor (
  input wire touch_in,
  output reg touch_out
);

  reg touch_detected;

  always @(posedge touch_in) begin
    touch_detected <= #1 touch_in;  // Delay the assignment by 1 time unit to avoid multiple edge sensitive events
  end

  always @(*) begin
    touch_out = touch_detected;
  end

endmodule