// SVA for piso_shift_register
// Bind these assertions to the DUT type
module piso_shift_register_sva (
    input  logic        clk,
    input  logic        reset,
    input  logic        shift_enable,
    input  logic [3:0]  parallel_in,
    input  logic        serial_out,
    input  logic [3:0]  shift_reg,
    input  logic        serial_out_reg
);

  // Basic sanity on control inputs
  assert property (@(posedge clk) !$isunknown(reset));
  assert property (@(posedge clk) !$isunknown(shift_enable));
  assert property (@(posedge clk) shift_enable |-> !$isunknown(parallel_in[0]));

  // Synchronous reset clears state and output on the next cycle
  assert property (@(posedge clk) reset |=> (shift_reg == 4'b0 && serial_out_reg == 1'b0 && serial_out == 1'b0));

  // serial_out must always mirror serial_out_reg
  assert property (@(posedge clk) serial_out == serial_out_reg);

  // No X/Z on key state while running
  assert property (@(posedge clk) disable iff (reset) !$isunknown({shift_reg, serial_out_reg, serial_out}));

  // Hold behavior: when not shifting, state holds and output reflects prior MSB
  assert property (@(posedge clk) disable iff (reset)
                   !shift_enable |=> (shift_reg == $past(shift_reg) &&
                                       serial_out == $past(shift_reg[3])));

  // Shift behavior: shift left, LSB loads parallel_in[0], output is prior MSB
  assert property (@(posedge clk) disable iff (reset)
                   shift_enable |=> (shift_reg == { $past(shift_reg[2:0]), $past(parallel_in[0]) } &&
                                      serial_out == $past(shift_reg[3])));

  // Coverage: reset, shift, hold, data 0/1, and output activity
  cover property (@(posedge clk) reset ##1 !reset);
  cover property (@(posedge clk) disable iff (reset) shift_enable && (parallel_in[0] == 1'b0));
  cover property (@(posedge clk) disable iff (reset) shift_enable && (parallel_in[0] == 1'b1));
  cover property (@(posedge clk) disable iff (reset) !shift_enable);
  cover property (@(posedge clk) disable iff (reset) shift_enable [*4]);
  cover property (@(posedge clk) disable iff (reset) ($rose(serial_out) or $fell(serial_out)));

endmodule

bind piso_shift_register piso_shift_register_sva sva_inst (.*);