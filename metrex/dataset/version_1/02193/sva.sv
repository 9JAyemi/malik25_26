// SVA for data_transfer
// Bind into the DUT; concise checks and coverage

module data_transfer_sva (
  input  logic        clk,
  input  logic        rst,
  input  logic        input_valid,
  input  logic [7:0]  input_data,
  input  logic [7:0]  output_data,
  input  logic        output_valid
);
  default clocking cb @(posedge clk); endclocking

  // Reset clears outputs next cycle
  a_reset_clears: assert property (rst |=> (output_valid == 1'b0 && output_data == 8'h00));

  // output_valid reflects prior input_valid when prior cycle not in reset
  a_valid_latency1: assert property ((!$past(rst)) |-> (output_valid == $past(input_valid)));

  // On a valid in prior cycle (and not in reset), output_data follows prior input_data
  a_data_follows:   assert property ((!$past(rst) && $past(input_valid)) |-> (output_data == $past(input_data)));

  // When no prior valid (and not in reset), hold data and deassert valid
  a_hold_no_valid:  assert property ((!$past(rst) && !$past(input_valid)) |-> (output_data == $past(output_data) && !output_valid));

  // No spurious valid immediately after a reset cycle
  a_no_valid_after_reset: assert property ($past(rst) |-> !output_valid);

  // Outputs are known when not in reset
  a_no_x_out: assert property (disable iff (rst) !$isunknown({output_valid, output_data}));

  // Coverage
  c_reset_then_transfer:  cover property (rst ##1 !rst ##1 input_valid ##1 output_valid);
  c_back_to_back_valids:  cover property (disable iff (rst) input_valid ##1 input_valid);
  c_idle_then_valid:      cover property (disable iff (rst) (!input_valid)[*2] ##1 input_valid);
  c_data_changes:         cover property (disable iff (rst) input_valid && $changed(input_data));
endmodule

bind data_transfer data_transfer_sva i_data_transfer_sva (.*);