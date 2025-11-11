// SVA for top_module and its submodules (bound at top for concision/coverage)

module top_module_sva (
  input logic        clk,
  input logic        reset,            // active-low synchronous reset
  input logic [7:0]  reg_input,
  input logic [31:0] byte_input,
  input logic [7:0]  func_output,
  input logic [7:0]  reg_output,       // internal of top_module
  input logic [31:0] byte_output       // internal of top_module
);
  default clocking cb @(posedge clk); endclocking

  // Functional correctness
  a_byte_reverse: assert property (byte_output ==
                                   {byte_input[7:0], byte_input[15:8], byte_input[23:16], byte_input[31:24]});

  a_or_correct:   assert property (func_output == (reg_output | byte_output[31:24]));

  // reg_with_reset: synchronous active-low behavior
  a_reg_reset_val: assert property (disable iff ($initstate)
                                    $past(reset)==0 |-> reg_output == 8'h34);

  a_reg_update:    assert property (disable iff ($initstate)
                                    $past(reset)==1 |-> reg_output == $past(reg_input));

  // X-prop sanity
  a_no_x_byte: assert property (!$isunknown(byte_input) |-> !$isunknown(byte_output));
  a_no_x_or:   assert property (!$isunknown({reg_output, byte_output[31:24]}) |-> !$isunknown(func_output));
  a_no_x_reg:  assert property (disable iff ($initstate)
                                ($past(reset)==1 && !$isunknown($past(reg_input))) |-> !$isunknown(reg_output));

  // Minimal yet meaningful coverage
  c_reset_assert:     cover property ($fell(reset));
  c_reset_deassert:   cover property ($rose(reset));
  c_byte_rev_change:  cover property ($changed(byte_input) &&
                                      byte_output == {byte_input[7:0], byte_input[15:8], byte_input[23:16], byte_input[31:24]});
  c_or_from_a_only:   cover property (byte_output[31:24]==8'h00 && reg_output!=8'h00 && func_output==reg_output);
  c_or_from_b_only:   cover property (reg_output==8'h00 && byte_output[31:24]!=8'h00 && func_output==byte_output[31:24]);
  c_or_both_contrib:  cover property (reg_output!=8'h00 && byte_output[31:24]!=8'h00 &&
                                      func_output != reg_output && func_output != byte_output[31:24]);
endmodule

// Bind into top so we can see internal wires and use the clock
bind top_module top_module_sva sva_i (
  .clk(clk),
  .reset(reset),
  .reg_input(reg_input),
  .byte_input(byte_input),
  .func_output(func_output),
  .reg_output(reg_output),
  .byte_output(byte_output)
);