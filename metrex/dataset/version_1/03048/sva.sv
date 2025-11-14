// SVA for ShiftLeft
module ShiftLeft_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  InVec,
  input logic        load,
  input logic        start,
  input logic        done,
  input logic [3:0]  OutVec,
  input logic [3:0]  reg_InVec,
  input logic [1:0]  shift_count,
  input logic [3:0]  shifted_value
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Basic correctness
  a_done_iff:       assert property (done == (shift_count == 2));
  a_cnt_range:      assert property (shift_count <= 2);
  a_out_sel_lt2:    assert property ((shift_count < 2) |-> (OutVec == reg_InVec));
  a_out_sel_eq2:    assert property ((shift_count == 2) |-> (OutVec == shifted_value && OutVec == {reg_InVec[1:0],2'b0}));
  a_done_out_zero:  assert property (done |-> (OutVec == 4'b0)); // 4-bit << 4 = 0

  // State update rules
  a_reset_vals:     assert property ($rose(reset) |=> (shift_count == 0 && reg_InVec == 4'b0 && done == 1'b0 && OutVec == 4'b0));

  a_load_vals:      assert property (load && !reset |=> (shift_count == 0 &&
                                                        reg_InVec == $past(InVec) &&
                                                        done == 1'b0 &&
                                                        OutVec == $past(InVec)));

  a_start_step:     assert property (!load && start && (shift_count < 2)
                                     |=> (reg_InVec == { $past(reg_InVec)[1:0], 2'b0} &&
                                          shift_count == $past(shift_count)+1));

  a_hold_noact:     assert property (!(load || (start && shift_count < 2))
                                     |=> ($stable(reg_InVec) && $stable(shift_count)));

  a_done_sticky:    assert property (done && !load
                                     |=> (done && shift_count == 2 && $stable(reg_InVec) && OutVec == 4'b0));

  // Functional coverage
  c_two_shifts_done: cover property (load ##1 start ##1 start ##0 done && OutVec == 4'b0);
  c_start_blocked:   cover property (done ##1 start ##1 done);
  c_idle_hold:       cover property (!(load || start) [*3] ##1 $stable(reg_InVec) && $stable(shift_count));

endmodule

// Bind into DUT
bind ShiftLeft ShiftLeft_sva i_shiftleft_sva (
  .clk(clk),
  .reset(reset),
  .InVec(InVec),
  .load(load),
  .start(start),
  .done(done),
  .OutVec(OutVec),
  .reg_InVec(reg_InVec),
  .shift_count(shift_count),
  .shifted_value(shifted_value)
);