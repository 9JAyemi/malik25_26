
module touch_sensor_interface (
  input sensor_type,
  input touch,
  output reg touched
);

  // Capacitive sensing algorithm
  reg cap_sense;
  always @ (posedge touch) begin
    if (sensor_type == 1'b1) begin
      cap_sense <= !cap_sense;
    end
  end

  // Resistive sensing algorithm
  reg res_sense;
  always @ (posedge touch) begin
    if (sensor_type == 1'b0) begin
      res_sense <= !res_sense;
    end
  end

  // Output signal
  always @ (*) begin
    if (sensor_type == 1'b1) begin
      touched = cap_sense;
    end else begin
      touched = res_sense;
    end
  end

endmodule
