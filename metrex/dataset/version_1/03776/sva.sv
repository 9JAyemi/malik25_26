// SVA for barrel_shifter. Bind this to the DUT.
// Example: bind barrel_shifter barrel_shifter_sva sva();

module barrel_shifter_sva (barrel_shifter dut);

  default clocking cb @(posedge $global_clock); endclocking

  // X-prop check: clean outputs when inputs are known
  ap_no_x: assert property (!$isunknown({dut.A,dut.B})) |-> ##0 !$isunknown({dut.abs_B,dut.stage1_out,dut.stage2_out,dut.result});

  // abs_B correctness
  ap_abs_pos: assert property (!dut.B[3]) |-> ##0 (dut.abs_B == dut.B);
  ap_abs_neg: assert property ( dut.B[3]) |-> ##0 (dut.abs_B == (~dut.B + 4'b0001));

  // Stage computations and pass-throughs
  ap_stage1_left:  assert property (!dut.B[3]) |-> ##0 (dut.stage1_out == (dut.A << dut.B));
  ap_stage1_right: assert property ( dut.B[3]) |-> ##0 (dut.stage1_out == (dut.A >> dut.abs_B));
  ap_stage2_passthru: assert property (1) |-> ##0 (dut.stage2_out == dut.stage1_out);
  ap_result_passthru: assert property (1) |-> ##0 (dut.result == dut.stage2_out);

  // Functional equivalence
  ap_result_func: assert property (1) |-> ##0 (dut.result == (dut.B[3] ? (dut.A >> dut.abs_B) : (dut.A << dut.B)));

  // Boundary semantics: shift amount >= width yields zero
  ap_left_ge_width_zero:  assert property (!dut.B[3] && (dut.B     >= 4)) |-> ##0 (dut.result == 4'b0000);
  ap_right_ge_width_zero: assert property ( dut.B[3] && (dut.abs_B >= 4)) |-> ##0 (dut.result == 4'b0000);

  // Identity when shift=0
  ap_shift0_identity: assert property (dut.B == 4'd0) |-> ##0 (dut.result == dut.A);

  // Coverage
  cp_left:  cover property (!dut.B[3]);
  cp_right: cover property ( dut.B[3]);
  cp_left_amts:  cover property (!dut.B[3] && (dut.B inside {4'd0,4'd1,4'd2,4'd3}));
  cp_right_amts: cover property ( dut.B[3] && (dut.abs_B inside {4'd1,4'd2,4'd3}));
  cp_ge_width:   cover property ((!dut.B[3] && dut.B>=4) or (dut.B[3] && dut.abs_B>=4));
  cp_neg_one:    cover property (dut.B == 4'b1111); // -1
  cp_neg_eight:  cover property (dut.B == 4'b1000); // -8

endmodule