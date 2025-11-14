// SVA for top_module
module top_module_sva (
  input clk,
  input areset,
  input load,
  input ena,
  input [3:0] data,
  input d,
  input [6:0] q,
  input [3:0] shift_reg,
  input [2:0] shift_reg_3
);
  default clocking cb @(posedge clk); endclocking

  bit past_v; initial past_v = 0;
  always @(posedge clk or posedge areset) if (areset) past_v <= 0; else past_v <= 1;

  // Async reset behavior
  assert property (@(posedge areset) 1 |-> ##0 (shift_reg == 4'b0));
  assert property (@(posedge clk) areset |-> ##0 (shift_reg == 4'b0));

  // 4-bit shift register behavior
  assert property (@(posedge clk) (!areset && ena && load)   |=> (shift_reg == $past(data)));
  assert property (@(posedge clk) (!areset && ena && !load)  |=> (shift_reg == $past({shift_reg[2:0], d})));
  assert property (@(posedge clk) (!areset && !ena)          |=> (shift_reg == $past(shift_reg)));

  // 3-bit shift register behavior (no reset)
  assert property (@(posedge clk) past_v |=> (shift_reg_3 == $past({shift_reg_3[1:0], d})));

  // Output mapping (OR 3'b0 is a no-op)
  assert property (@(posedge clk) ##0 (q == {shift_reg, shift_reg_3}));
  assert property (@(posedge areset) 1 |-> ##0 (q == {shift_reg, shift_reg_3}));

  // X-checks on controls/data when used
  assert property (@(posedge clk) !$isunknown({areset, ena, load}));
  assert property (@(posedge clk) (!areset && ena && load) |-> !$isunknown(data));
  assert property (@(posedge clk) (!areset && ena)         |-> !$isunknown(d));

  // Coverage
  cover property (@(posedge areset) 1);
  cover property (@(posedge clk) (!areset && ena && load));
  cover property (@(posedge clk) (!areset && ena && !load));
  cover property (@(posedge clk) (!areset && !ena));
endmodule

bind top_module top_module_sva u_top_module_sva (
  .clk(clk), .areset(areset), .load(load), .ena(ena), .data(data), .d(d),
  .q(q), .shift_reg(shift_reg), .shift_reg_3(shift_reg_3)
);