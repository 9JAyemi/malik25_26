// SVA for pulse_generator
module pulse_generator_sva(input logic clk, input logic pulse, input logic [4:0] counter);

  default clocking cb @(posedge clk); endclocking

  // Sanity/range
  a_no_x:    assert property (!$isunknown({pulse,counter}));
  a_range:   assert property (counter <= 5'd16);

  // Counter progression
  a_0_to_1:  assert property ((counter==5'd0)  |-> ##1 counter==5'd1);
  a_inc_mid: assert property ((counter inside {[5'd1:5'd15]}) |-> ##1 counter == $past(counter)+1);
  a_wrap:    assert property ((counter==5'd16) |-> ##1 counter==5'd0);

  // Pulse behavior and correlation
  a_pulse_only_on_16: assert property ((counter!=5'd16) |-> ##1 pulse==1'b0);
  a_pulse_on_16:      assert property ((counter==5'd16) |-> ##1 pulse==1'b1);
  a_pulse_single:     assert property (pulse |-> ##1 !pulse);
  a_pulse_origin:     assert property ($rose(pulse) |-> $past(counter)==5'd16);
  a_pulse_state:      assert property (pulse |-> (counter==5'd0)); // when pulse is sampled high, counter is 0

  // Periodicity: one-cycle high every 17 cycles
  a_pulse_period:     assert property ($rose(pulse) |-> (!pulse[*16]) ##1 pulse);

  // Coverage
  c_pulse_seen:       cover property ($rose(pulse));
  c_periodic:         cover property ($rose(pulse) ##1 !pulse[*15] ##1 !pulse ##1 pulse);
  c_counter_walk:     cover property (
                        (counter==5'd0) ##1 (counter==5'd1) ##1 (counter==5'd2) ##1 (counter==5'd3) ##1
                        (counter==5'd4) ##1 (counter==5'd5) ##1 (counter==5'd6) ##1 (counter==5'd7) ##1
                        (counter==5'd8) ##1 (counter==5'd9) ##1 (counter==5'd10) ##1 (counter==5'd11) ##1
                        (counter==5'd12) ##1 (counter==5'd13) ##1 (counter==5'd14) ##1 (counter==5'd15) ##1
                        (counter==5'd16) ##1 (counter==5'd0)
                      );

endmodule

bind pulse_generator pulse_generator_sva sva_inst(.clk(clk), .pulse(pulse), .counter(counter));