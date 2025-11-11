// SVA for shift_register
// Bind this checker and connect a clock from your environment.
// Example:
//   bind shift_register shift_register_sva #(.WIDTH(4)) u_sva (
//     .clk(tb_clk), .data_in(data_in), .shift(shift), .data_out(data_out), .shift_reg(shift_reg)
//   );

module shift_register_sva #(parameter int WIDTH = 4) (
  input  logic                   clk,
  input  logic [WIDTH-1:0]       data_in,
  input  logic                   shift,
  input  logic [WIDTH-1:0]       data_out,
  input  logic [WIDTH-1:0]       shift_reg
);
  default clocking cb @(posedge clk); endclocking

  // Sanity
  a_init_zero:     assert property ($initstate |-> data_out == '0);
  a_known_inputs:  assert property (!$isunknown(shift) && !$isunknown(data_in));
  a_known_output:  assert property (!$isunknown(data_out));
  a_out_matches_q: assert property (data_out == shift_reg);

  // Functionality
  a_load:  assert property (shift == 1'b0 |=> data_out == $past(data_in));
  a_shift: assert property (shift == 1'b1 |=> data_out == { $past(data_out[WIDTH-2:0]), 1'b0 });
  a_load_then_shift: assert property ($past(shift)==1'b0 && shift==1'b1 |-> data_out == { $past(data_in[WIDTH-2:0]), 1'b0 });
  a_shift_clear: assert property (shift[*WIDTH] |=> data_out == '0);

  // Coverage
  c_nonzero_load:      cover property (shift==1'b0 && data_in != '0);
  c_load_then_shift:   cover property (shift==1'b0 ##1 shift==1'b1);
  c_shift_msb0_case:   cover property (shift==1'b1 && $past(data_out[WIDTH-1])==1'b0);
  c_shift_msb1_case:   cover property (shift==1'b1 && $past(data_out[WIDTH-1])==1'b1);
  c_shift_streak_zero: cover property (shift[*WIDTH] ##1 (data_out=='0));
endmodule