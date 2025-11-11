module touch_sensor #(
  parameter n = 4, // number of touch sensor signals
  parameter m = 2 // number of digital output signals
) (
  input [n-1:0] touch_sensors,
  input clk,
  output reg [m-1:0] digital_outputs
);

// Capacitive touch technology implementation
reg [n-1:0] touch_sensors_prev;
reg [m-1:0] digital_outputs_prev;
reg [m-1:0] digital_outputs_curr;

always @(*) begin
  digital_outputs_curr = {touch_sensors} ^ {touch_sensors_prev};
end

always @(posedge clk) begin
  touch_sensors_prev <= touch_sensors;
  digital_outputs_prev <= digital_outputs_curr;
  digital_outputs <= digital_outputs_curr;
end

endmodule