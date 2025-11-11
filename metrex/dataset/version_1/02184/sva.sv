// SystemVerilog Assertions for the given design
// Bind by module type to cover all instances concisely

// Checker for shift_register
module shift_register_sva (
  input clk,
  input reset,          // active-low async
  input load,
  input [3:0] load_value,
  input [3:0] shift_out
);
  default clocking @(posedge clk); endclocking

  // Asynchronous reset clears immediately and holds while low
  a_sr_async_clear_now:   assert property (@(negedge reset) shift_out == 4'b0);
  a_sr_hold_zero_on_rst:  assert property (@(posedge clk) !reset |-> shift_out == 4'b0);

  // Load takes effect next cycle when not in reset
  a_sr_load:              assert property (disable iff (!reset)
                                           load |=> shift_out == $past(load_value));

  // Shift-left with zero-in when not loading
  a_sr_shift:             assert property (disable iff (!reset)
                                           !load |=> shift_out == {$past(shift_out[2:0]), 1'b0});

  // No X on output at active edges
  a_sr_no_x:              assert property (@(posedge clk) !$isunknown(shift_out));

  // Coverage
  c_sr_reset:             cover property (@(negedge reset) 1);
  c_sr_load_then_shift:   cover property (disable iff (!reset) load ##1 !load[*2]);
  c_sr_shift_to_zero:     cover property (disable iff (!reset) !load[*4] ##1 shift_out == 4'b0);
endmodule

// Checker for d_flip_flop
module d_flip_flop_sva (
  input clk,
  input d,
  input aset,            // synchronous set
  input areset,          // active-low async reset
  input q
);
  default clocking @(posedge clk); endclocking

  // Asynchronous reset clears immediately and holds while low
  a_dff_async_clear_now:  assert property (@(negedge areset) q == 1'b0);
  a_dff_hold_zero_on_rst: assert property (@(posedge clk) !areset |-> q == 1'b0);

  // Synchronous set when not in async reset
  a_dff_sync_set:         assert property (disable iff (!areset)
                                           aset |=> q == 1'b1);

  // Data capture when neither async reset nor sync set
  a_dff_data_cap:         assert property (disable iff (!areset)
                                           !aset |=> q == $past(d));

  // Reset dominates set
  a_dff_reset_over_set:   assert property (@(posedge clk) (!areset && aset) |-> q == 1'b0);

  // No X on output at active edges
  a_dff_no_x:             assert property (@(posedge clk) !$isunknown(q));

  // Coverage
  c_dff_areset:           cover property (@(negedge areset) 1);
  c_dff_set:              cover property (disable iff (!areset) aset);
  c_dff_data_0to1:        cover property (disable iff (!areset)
                                           !aset && $past(q)==1'b0 && $past(d)==1'b1 |=> q==1'b1);
  c_dff_data_1to0:        cover property (disable iff (!areset)
                                           !aset && $past(q)==1'b1 && $past(d)==1'b0 |=> q==1'b0);
endmodule

// Bind to all instances of each module type
bind shift_register shift_register_sva sva_shift (
  .clk(clk),
  .reset(reset),
  .load(load),
  .load_value(load_value),
  .shift_out(shift_out)
);

bind d_flip_flop d_flip_flop_sva sva_dff (
  .clk(clk),
  .d(d),
  .aset(aset),
  .areset(areset),
  .q(q)
);