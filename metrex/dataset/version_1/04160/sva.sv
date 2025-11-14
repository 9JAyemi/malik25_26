// SVA checker for shift_register
module shift_register_sva (
  input  logic        clk,
  input  logic        load,
  input  logic        shift_enable,
  input  logic [3:0]  data_in,
  input  logic [3:0]  data_out,
  input  logic [3:0]  shift_reg
);
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Core functional correctness
  // data_out is always the previous value of shift_reg
  assert property (data_out == $past(shift_reg));

  // Load updates shift_reg on next cycle (priority over shift)
  assert property (load |-> ##1 (shift_reg == $past(data_in)));

  // Shift with zero-fill when not loading
  assert property ((!load && shift_enable) |-> ##1
                   (shift_reg == {$past(shift_reg[2:0]), 1'b0}));

  // Hold when neither load nor shift_enable
  assert property ((!load && !shift_enable) |-> ##1
                   (shift_reg == $past(shift_reg)));

  // No spurious change: shift_reg only changes if load or shift_enable were set
  assert property (((shift_reg != $past(shift_reg))) |-> $past(load || shift_enable));

  // Coverage
  cover property (load);
  cover property (!load && shift_enable);
  cover property (!load && !shift_enable);
  cover property (load && shift_enable); // priority case
  cover property (load ##1 (!load && shift_enable)[*4]); // load then 4 shifts
  cover property ($changed(shift_reg) ##1 (data_out == $past(shift_reg)));

endmodule

// Bind into the DUT
bind shift_register shift_register_sva i_shift_register_sva (
  .clk(clk),
  .load(load),
  .shift_enable(shift_enable),
  .data_in(data_in),
  .data_out(data_out),
  .shift_reg(shift_reg)
);