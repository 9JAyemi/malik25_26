// SVA for resettable_register
module resettable_register_sva (
  input logic clk, reset, set, clear,
  input logic data_in,
  input logic data_out
);

  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1'b1;

  // Priority/functional correctness
  a_reset_zero: assert property (reset |-> data_out == 1'b0);
  a_set_one:    assert property (!reset && set  |-> data_out == 1'b1);
  a_clear_zero: assert property (!reset && !set && clear |-> data_out == 1'b0);
  a_hold:       assert property (past_valid && !reset && !set && !clear |-> data_out == $past(data_out));

  // Output only changes when a control is asserted (data_in has no effect)
  a_change_requires_ctrl: assert property (past_valid && (data_out != $past(data_out)) |-> (reset || set || clear));

  // Sanity: no X/Z on key signals
  a_no_x_out:   assert property (!$isunknown(data_out));
  a_no_x_ctrls: assert property (!$isunknown({reset,set,clear}));

  // Coverage: hit each branch and key transitions
  c_reset:        cover property (reset);
  c_set_only:     cover property (!reset && set && !clear);
  c_clear_only:   cover property (!reset && !set && clear);
  c_set_and_clear:cover property (!reset && set && clear); // set wins over clear
  c_hold_path:    cover property (past_valid && !reset && !set && !clear ##1 !reset && !set && !clear);
  c_out_rise:     cover property (past_valid && !$past(data_out) && data_out);
  c_out_fall:     cover property (past_valid && $past(data_out) && !data_out);

endmodule

// Bind into DUT
bind resettable_register resettable_register_sva sva_i(.*);