module motor_control (
  input step,
  input dir,
  output ctrl
);

  parameter steps_per_rev = 200; // number of steps per revolution
  
  reg [7:0] count = 0; // 8-bit counter for pulse generation
  reg direction = 1; // flip-flop to store direction of stepper motor
  
  always @(posedge step) begin
    if (count == steps_per_rev) begin
      count <= 0;
    end else begin
      count <= count + 1;
    end
  end
  
  always @(posedge step) begin
    if (dir == 1) begin
      direction <= ~direction;
    end
  end
  
  assign ctrl = (count == steps_per_rev/2) ? direction : ~direction; // generate pulse train
  
endmodule