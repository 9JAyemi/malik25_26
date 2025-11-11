// SVA for the provided design

// shift_register
module shift_register_sva(input clk, input reset, input data_in, input [2:0] q);
  // Async reset clears immediately and while high
  assert property (@(posedge reset) ##0 (q == 3'b000));
  assert property (@(posedge clk) reset |-> (q == 3'b000));

  // Shift behavior on clocks when not in reset
  assert property (@(posedge clk) disable iff (reset)
                   q == { $past(q[1:0]), $past(data_in) });

  // Coverage: observe a 1 entering and reaching MSB in 2 cycles; reset pulse
  cover property (@(posedge clk) disable iff (reset) data_in ##2 q[2]);
  cover property (@(posedge reset) 1);
endmodule
bind shift_register shift_register_sva u_shift_register_sva(.*);

// d_flip_flop
module d_flip_flop_sva(input clk, input reset, input d, input q);
  assert property (@(posedge reset) ##0 (q == 1'b0));
  assert property (@(posedge clk) reset |-> (q == 1'b0));

  assert property (@(posedge clk) disable iff (reset) q == $past(d));

  // Coverage: q toggles 0->1->0 across cycles
  cover property (@(posedge clk) disable iff (reset) $rose(q) ##1 $fell(q));
endmodule
bind d_flip_flop d_flip_flop_sva u_d_flip_flop_sva(.*);

// functional_module
module functional_module_sva(input [2:0] shift_register_out,
                             input d_flip_flop_out,
                             input [2:0] or_out);
  // Bitwise OR with zero-extended d_flip_flop_out
  assert property (@(*) or_out == (shift_register_out | {2'b00, d_flip_flop_out}));

  // Coverage: OR drives bit0 when SR bit0=0 and DFF=1
  cover property (@(*) (shift_register_out[0]==0 && d_flip_flop_out==1 && or_out[0]==1));
endmodule
bind functional_module functional_module_sva u_functional_module_sva(.*);

// control_logic
module control_logic_sva(input select,
                         input [2:0] shift_register_out,
                         input d_flip_flop_out,
                         input [2:0] functional_out,
                         input [2:0] q);
  // Pure combinational mux behavior
  assert property (@(*) q == (select ? functional_out : shift_register_out));

  // Coverage: exercise both mux paths
  cover property (@(posedge select) 1);
  cover property (@(negedge select) 1);
endmodule
bind control_logic control_logic_sva u_control_logic_sva(.*);

// top_module
module top_module_sva(input clk, input reset, input d, input select, input q,
                      input [2:0] shift_register_out,
                      input [2:0] functional_out,
                      input [2:0] ctrl_logic_out);
  // Wiring correctness
  assert property (@(*) q == ctrl_logic_out[2]);

  // End-to-end: q always equals SR MSB (functional path can't change bit[2])
  assert property (@(*) q == shift_register_out[2]);

  // Coverage: input bit reaches q after two clocks (with reset excluded)
  cover property (@(posedge clk) disable iff (reset) d ##2 q);
endmodule
bind top_module top_module_sva u_top_module_sva(
  .clk(clk), .reset(reset), .d(d), .select(select), .q(q),
  .shift_register_out(shift_register_out),
  .functional_out(functional_out),
  .ctrl_logic_out(ctrl_logic_out)
);