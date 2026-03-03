// SVA for shift_register_4bit
module shift_register_4bit_sva (
  input clk,
  input rst,
  input load,
  input shift,
  input [3:0] data_in,
  input [3:0] data_out
);
  default clocking cb @(posedge clk); endclocking

  // Reset drives zero
  a_reset_zero: assert property (!rst |-> data_out == 4'b0);

  // No X on output when active
  a_no_x_active: assert property (rst |-> !$isunknown(data_out));

  // Load has priority (even if shift is also asserted)
  a_load_prio: assert property (rst && load |=> data_out == $past(data_in));

  // Shift-left with zero-insert when no load
  a_shift_left: assert property (rst && !load && shift
                                 |=> data_out == {$past(data_out[2:0]), 1'b0});

  // Hold value when neither load nor shift
  a_hold: assert property (rst && !load && !shift |=> data_out == $past(data_out));

  // Functional coverage
  c_reset_cycle:     cover property ($fell(rst) ##1 $rose(rst));
  c_load:            cover property (rst && load);
  c_shift:           cover property (rst && !load && shift);
  c_hold:            cover property (rst && !load && !shift);
  c_load_and_shift:  cover property (rst && load && shift);
  // From a non-zero load, four shifts flush to zero
  c_flush_to_zero:   cover property (rst && load && (data_in != 4'b0)
                                     ##1 (rst && !load && shift)[*4]
                                     ##1 data_out == 4'b0);
endmodule

bind shift_register_4bit shift_register_4bit_sva sva (.*);