// SVA for rotator_adder
module rotator_adder_sva;
  // Bound into rotator_adder scope; direct access to DUT signals
  default clocking @(posedge clk); endclocking
  default disable iff (reset);

  // Rotation on load
  a_rot_00: assert property (load && (ena==2'b00) |=> rotated_data == $past(data));
  a_rot_01: assert property (load && (ena==2'b01) |=> rotated_data == { $past(data[31:0]),  $past(data[99:32]) });
  a_rot_10: assert property (load && (ena==2'b10) |=> rotated_data == { $past(data[67:0]),  $past(data[99:68]) });
  a_rot_11: assert property (load && (ena==2'b11) |=> rotated_data == { $past(data[33:0]),  $past(data[99:34]) });

  // Hold when not loading
  a_hold:   assert property (!load |=> rotated_data == $past(rotated_data));

  // Pipeline checks
  a_add:    assert property (!$past(reset) |-> adder_out == $past(rotated_data[31:0]) + 32'd12345678);
  a_q:      assert property (!$past(reset) |-> q == $past(adder_out));
  a_e2e:    assert property (!$past(reset,2,reset) |-> q == $past(rotated_data[31:0] + 32'd12345678, 2, reset));

  // Reset behavior
  a_rst_regs:    assert property (reset |=> rotated_data==100'd0 && adder_out==32'd0);
  a_rst_q_hold:  assert property (reset |=> q == $past(q));

  // Functional coverage
  c_reset:   cover property (reset);
  c_load00:  cover property (load && ena==2'b00);
  c_load01:  cover property (load && ena==2'b01);
  c_load10:  cover property (load && ena==2'b10);
  c_load11:  cover property (load && ena==2'b11);
  c_hold:    cover property (!load);
  c_pipe:    cover property (!$past(reset,2,reset) && q == $past(rotated_data[31:0] + 32'd12345678, 2, reset));
  c_b2b:     cover property (load ##1 load);
endmodule

bind rotator_adder rotator_adder_sva sva();