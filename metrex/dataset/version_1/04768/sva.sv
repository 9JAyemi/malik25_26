// SVA for motor_control
module motor_control_sva(
  input logic        clk,
  input logic [3:0]  voltage,
  input logic [3:0]  speed,
  input logic        warning
);

  default clocking cb @(posedge clk); endclocking

  // Forward functional mapping (voltage -> next-cycle outputs)
  assert property ( (voltage < 4)             |=> (speed==4'b0000 && warning==1'b0) );
  assert property ( (voltage inside {[4:5]})  |=> (speed==4'b0100 && warning==1'b0) );
  assert property ( (voltage inside {[6:7]})  |=> (speed==4'b1111 && warning==1'b0) );
  assert property ( (voltage inside {[8:15]}) |=> (speed==4'b1111 && warning==1'b1) );

  // Safety/invariants
  assert property ( !$isunknown({speed,warning}) |-> (speed inside {4'b0000,4'b0100,4'b1111}) );
  assert property ( warning |-> (speed==4'b1111) );

  // Reverse check (guard first cycle) - warning only comes from voltage >= 8
  assert property ( (!$isunknown($past(voltage))) && warning |-> ($past(voltage inside {[8:15]})) );

  // Functional coverage (buckets and thresholds)
  cover property ( (voltage < 4)             ##1 (speed==4'b0000 && warning==1'b0) );
  cover property ( (voltage inside {[4:5]})  ##1 (speed==4'b0100 && warning==1'b0) );
  cover property ( (voltage inside {[6:7]})  ##1 (speed==4'b1111 && warning==1'b0) );
  cover property ( (voltage inside {[8:15]}) ##1 (speed==4'b1111 && warning==1'b1) );

  // Threshold transition behaviors
  cover property ( (voltage==3) ##1 (voltage==4 && speed==4'b0000) ##1 (speed==4'b0100) );
  cover property ( (voltage==5) ##1 (voltage==6 && speed==4'b0100) ##1 (speed==4'b1111 && warning==1'b0) );
  cover property ( (voltage==7) ##1 (voltage==8 && speed==4'b1111 && warning==1'b0) ##1 (warning==1'b1) );

endmodule

bind motor_control motor_control_sva u_motor_control_sva(
  .clk(clk),
  .voltage(voltage),
  .speed(speed),
  .warning(warning)
);