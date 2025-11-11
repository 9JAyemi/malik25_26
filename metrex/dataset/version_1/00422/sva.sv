// SVA for left_shift_register
module left_shift_register_sva (
  input logic        clk,
  input logic        reset,       // active-low
  input logic [31:0] data,
  input logic [4:0]  shift_amount,
  input logic [31:0] shifted_data
);

  default clocking cb @(posedge clk); endclocking
  // Assertions that are synchronous to clk are disabled during reset low
  default disable iff (!reset);

  // No X/Z on key signals when active
  a_no_x_inputs:  assert property ( !$isunknown({data, shift_amount}) );
  a_no_x_output:  assert property ( !$isunknown(shifted_data) );

  // Functional: result equals shift, with guard for out-of-range (matches DUT)
  a_shift_func: assert property (
    shifted_data == ((shift_amount >= 5'd32) ? 32'h0 : (data << shift_amount))
  );

  // Async reset immediately forces zero
  a_async_reset_zero: assert property (@(negedge reset) ##0 (shifted_data == 32'h0));

  // While reset is low, output sampled on each clk must be zero
  a_in_reset_zero_on_clk: assert property (@(posedge clk) !reset |-> (shifted_data == 32'h0));

  // Sanity: shifting zero always yields zero
  a_zero_in_zero_out: assert property ( (data == 32'h0) |-> (shifted_data == 32'h0) );

  // Sanity: shift by 0 is pass-through
  a_shift0_identity: assert property ( (shift_amount == 5'd0) |-> (shifted_data == data) );

  // Coverage
  c_reset_seq:    cover property (@(posedge clk) !reset ##1 reset);
  c_shift_0:      cover property ( reset && (shift_amount == 5'd0)  && (data != 32'h0) && (shifted_data == data) );
  c_shift_31:     cover property ( reset && (shift_amount == 5'd31) );
  c_nonzero_out:  cover property ( reset && (shifted_data != 32'h0) );

endmodule

// Bind into the DUT
bind left_shift_register left_shift_register_sva u_left_shift_register_sva (
  .clk(clk),
  .reset(reset),
  .data(data),
  .shift_amount(shift_amount),
  .shifted_data(shifted_data)
);