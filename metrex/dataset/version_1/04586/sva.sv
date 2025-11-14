// SVA for top_module: concise, high-quality checks and coverage
`ifndef TOP_MODULE_SVA_SVH
`define TOP_MODULE_SVA_SVH

module top_module_sva;
  default clocking cb @(posedge clk); endclocking

  // start checking after first clock to make $past well-defined
  logic init_done;
  initial init_done = 1'b0;
  always @(posedge clk) init_done <= 1'b1;
  default disable iff (!init_done);

  // Control must be known
  a_ctrl_known:        assert property (!$isunknown({load, ena}));

  // Structural consistency
  a_q_matches_reg:     assert property (q == shift_reg);
  a_qreg_matches_reg:  assert property (q_reg == reg_data);
  a_and_correct:       assert property (and_output == (q[7:0] & q_reg));

  // Load behavior
  a_load_q:            assert property (load |=> q     == $past(data));
  a_load_qreg:         assert property (load |=> q_reg == $past(d));

  // Hold behavior (both 00 and 11) and reg hold when not loading
  a_hold_00:           assert property ((!load && (ena==2'b00)) |=> q == $past(q));
  a_hold_11:           assert property ((!load && (ena==2'b11)) |=> q == $past(q));
  a_reg_hold:          assert property ((!load)                |=> q_reg == $past(q_reg));

  // Rotate behavior
  a_rot_left:          assert property ((!load && (ena==2'b01)) |=> q == {$past(q[98:0]), $past(q[99])});
  a_rot_right:         assert property ((!load && (ena==2'b10)) |=> q == {$past(q[0]),    $past(q[99:1])});

  // 100-step rotation returns to original
  sequence left100;    (!load && (ena==2'b01))[*100]; endsequence
  sequence right100;   (!load && (ena==2'b10))[*100]; endsequence
  a_rot_left_100:      assert property (left100  |=> q == $past(q,100));
  a_rot_right_100:     assert property (right100 |=> q == $past(q,100));

  // Functional coverage
  c_load:              cover  property (load);
  c_hold00:            cover  property (!load && (ena==2'b00));
  c_hold11:            cover  property (!load && (ena==2'b11));
  c_shift_l:           cover  property (!load && (ena==2'b01));
  c_shift_r:           cover  property (!load && (ena==2'b10));
  c_l_then_r:          cover  property ((!load && (ena==2'b01)) ##1 (!load && (ena==2'b10)));
endmodule

bind top_module top_module_sva sva();

`endif