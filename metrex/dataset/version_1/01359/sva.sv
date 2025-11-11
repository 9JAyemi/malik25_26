// SVA for shift_reg. Bind into DUT or instantiate alongside.

module shift_reg_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        load,
  input  logic [3:0]  data_in,
  input  logic [3:0]  shift_out
);

  // Asynchronous reset drives 0 immediately
  ap_async_reset: assert property (@(posedge reset) ##0 (shift_out == 4'b0000));

  // While reset asserted at clk edge, state is 0 on the following cycle
  ap_reset_holds:  assert property (@(posedge clk) reset |=> (shift_out == 4'b0000));

  // No X on controls; no X on I/O when not in reset
  ap_no_x_ctrl:    assert property (@(posedge clk) !$isunknown({reset,load}));
  ap_no_x_io:      assert property (@(posedge clk) !reset |-> !$isunknown({data_in,shift_out}));

  // Load behavior (reset low): capture data_in on next cycle
  ap_load_cap:     assert property (@(posedge clk) disable iff (reset)
                                    load |=> (shift_out == $past(data_in)));

  // Rotate-left by 1 when not loading (reset low)
  ap_rotate:       assert property (@(posedge clk) disable iff (reset)
                                    !load |=> (shift_out == {$past(shift_out[2:0]), $past(shift_out[3])}));

  // 4-cycle rotational periodicity under continuous rotate (reset low)
  ap_period4:      assert property (@(posedge clk) disable iff (reset)
                                    (!load)[*4] |=> (shift_out == $past(shift_out,4)));

  // Coverage
  cp_async_reset:  cover  property (@(posedge reset) 1);
  cp_load:         cover  property (@(posedge clk) !reset && load);
  cp_rotate4:      cover  property (@(posedge clk) disable iff (reset) (!load)[*4]);
  cp_load_then_rot:cover  property (@(posedge clk) disable iff (reset)
                                    load ##1 (!load)[*4]);

endmodule

bind shift_reg shift_reg_sva u_shift_reg_sva (.clk, .reset, .load, .data_in, .shift_out);