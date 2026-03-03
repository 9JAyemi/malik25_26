// SVA for shift_register: concise, high-quality checks and coverage
module shift_register_sva (
  input logic        clk,
  input logic        reset,      // async active-high
  input logic        shift,
  input logic        shift_in,
  input logic [7:0]  data_out
);
  default clocking cb @(posedge clk); endclocking

  // Basic sanity/X checks
  ap_inputs_known:   assert property (!$isunknown({reset,shift,shift_in}));
  ap_out_known:      assert property (disable iff (reset) !$isunknown(data_out));

  // Asynchronous reset must drive zeros immediately
  ap_async_reset:    assert property (@(posedge reset) data_out == 8'b0);

  // While reset is sampled high at clk, output is 0 in the same cycle
  ap_sync_reset:     assert property (reset |=> data_out == 8'b0);

  // Core shift behavior (all cycles out of reset):
  // Upper bits move up by one every cycle (independent of shift/shift_in)
  ap_shift_move:     assert property (disable iff (reset)
                                      1'b1 |-> ##1 data_out[7:1] == $past(data_out[6:0]));

  // LSB insert rules
  ap_lsb_zero_ins:   assert property (disable iff (reset)
                                      shift |-> ##1 data_out[0] == 1'b0);

  ap_lsb_data_ins:   assert property (disable iff (reset)
                                      !shift |-> ##1 data_out[0] == $past(shift_in));

  // Optional full-vector equivalence (redundant but strong)
  ap_vec_zero_ins:   assert property (disable iff (reset)
                                      shift |-> ##1 data_out == {$past(data_out[6:0]),1'b0});
  ap_vec_data_ins:   assert property (disable iff (reset)
                                      !shift |-> ##1 data_out == {$past(data_out[6:0]),$past(shift_in)});

  // Coverage: exercise both insertion paths
  cv_zero_insert:    cover  property (disable iff (reset)
                                      shift ##1 (data_out[0] == 1'b0));

  cv_data_insert:    cover  property (disable iff (reset)
                                      (!shift && shift_in) ##1 (data_out[0] == 1'b1));

endmodule

// Bind into DUT
bind shift_register shift_register_sva u_shift_register_sva (.*);