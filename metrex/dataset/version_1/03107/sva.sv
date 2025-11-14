// SVA for shifter (bindable). Provide clk/rst_n from TB.
module shifter_sva(input logic clk, input logic rst_n);
  default clocking cb @(posedge clk); endclocking

  // Expected combinational result
  let exp_res =
      (shift_direction == 2'b00) ? (data_in >>  shift_amount) :
      (shift_direction == 2'b01) ? (data_in <<  shift_amount) :
      (shift_direction == 2'b10) ? ($signed(data_in) >>> shift_amount) :
                                   32'h0;

  // X-prop hygiene: known inputs imply known combinational internals/outputs
  a_no_x: assert property (disable iff (!rst_n)
                           !$isunknown({data_in, shift_amount, shift_direction})
                           |-> !$isunknown({stage1_out, stage2_out, stage3_out, result, zero}));

  // Functional correctness
  a_func:    assert property (disable iff (!rst_n) result == exp_res);

  // Pipeline propagation equivalence
  a_stg12:   assert property (disable iff (!rst_n) stage2_out == stage1_out);
  a_stg23:   assert property (disable iff (!rst_n) stage3_out == stage2_out);
  a_out_eq:  assert property (disable iff (!rst_n) result     == stage3_out);

  // Zero flag correctness
  a_zero:    assert property (disable iff (!rst_n) zero == (result == 32'h0));

  // Arithmetic-right sign-extension (for nonzero shifts)
  a_asr_se:  assert property (disable iff (!rst_n)
                              (shift_direction == 2'b10 && shift_amount != 5'd0)
                              |-> (result[31 -: shift_amount] == {shift_amount{data_in[31]}}));

  // Coverage: directions
  c_dir_lr:  cover property (shift_direction == 2'b00);
  c_dir_ll:  cover property (shift_direction == 2'b01);
  c_dir_ar:  cover property (shift_direction == 2'b10);
  c_dir_def: cover property (shift_direction == 2'b11);

  // Coverage: shift extremes and flags
  c_amt0:        cover property (shift_amount == 5'd0);
  c_amt31:       cover property (shift_amount == 5'd31);
  c_lr_amt31:    cover property (shift_direction == 2'b00 && shift_amount == 5'd31);
  c_ll_amt31:    cover property (shift_direction == 2'b01 && shift_amount == 5'd31);
  c_ar_neg:      cover property (shift_direction == 2'b10 && data_in[31] && shift_amount inside {[1:31]});
  c_zero_set:    cover property (zero);
  c_zero_clear:  cover property (!zero);
endmodule

bind shifter shifter_sva u_shifter_sva(.clk(clk), .rst_n(rst_n));