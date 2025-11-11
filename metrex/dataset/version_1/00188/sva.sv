// SVA for top_module and sub-functionality
module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [31:0] data,
  input  logic [4:0]  shift_amount,
  input  logic        shift_direction,
  input  logic        load,
  input  logic        up_down,
  input  logic [3:0]  count,
  input  logic [31:0] shifted_output,
  input  logic [31:0] final_output
);

  default clocking cb @(posedge clk); endclocking

  // Basic sanity/X checks
  a_ctrl_known:   assert property (!$isunknown({reset, shift_direction, load, up_down, shift_amount})); 
  a_no_x_outputs: assert property (!reset |-> !$isunknown({count, shifted_output, final_output}));

  // up_down_counter behavior
  a_reset: assert property (reset |-> count == 4'h0);

  a_load:  assert property (!reset && load |-> count == data[3:0]);

  a_inc:   assert property (disable iff (reset)
                            (!load && up_down)
                            |-> count == (($past(count,1,4'h0) + 4'd1) & 4'hF));

  a_dec:   assert property (disable iff (reset)
                            (!load && !up_down)
                            |-> count == (($past(count,1,4'h0) - 4'd1) & 4'hF));

  // barrel_shifter correctness (sampled at clk edge)
  a_bs_left:  assert property (shift_direction == 1'b0 |-> shifted_output == (data << shift_amount));
  a_bs_right: assert property (shift_direction == 1'b1 |-> shifted_output == (data >> shift_amount));

  // bitwise_and behavior (note: {{4{count}}} is 16-bit replicated mask, zero-extended to 32)
  a_and_upper_zero: assert property (final_output[31:16] == 16'h0000);
  a_and_lower:      assert property (final_output[15:0]  == (shifted_output[15:0] & {4{count}}));
  a_and_equiv:      assert property (final_output == (shifted_output & {{4{count}}}));

  // Key coverage
  c_bs_left0:   cover property (shift_direction==0 && shift_amount==5'd0);
  c_bs_left31:  cover property (shift_direction==0 && shift_amount==5'd31);
  c_bs_right0:  cover property (shift_direction==1 && shift_amount==5'd0);
  c_bs_right31: cover property (shift_direction==1 && shift_amount==5'd31);

  c_load:       cover property (!reset && load && !$isunknown(data[3:0]));
  c_inc_wrap:   cover property (disable iff (reset)
                                (!load && up_down && $past(count,1,4'h0)==4'hF && count==4'h0));
  c_dec_wrap:   cover property (disable iff (reset)
                                (!load && !up_down && $past(count,1,4'h0)==4'h0 && count==4'hF));

  c_mask_mix:   cover property (!reset && count==4'hA &&
                                shifted_output[15:0] != 16'h0000 &&
                                shifted_output[15:0] != 16'hFFFF);

endmodule

// Bind into DUT
bind top_module top_module_sva sva (
  .clk(clk),
  .reset(reset),
  .data(data),
  .shift_amount(shift_amount),
  .shift_direction(shift_direction),
  .load(load),
  .up_down(up_down),
  .count(count),
  .shifted_output(shifted_output),
  .final_output(final_output)
);