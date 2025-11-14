// SVA for top_module
module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [7:0]  data_in,
  input logic        select,
  input logic [7:0]  final_output,
  input logic [1:0]  out2,
  input logic [1:0]  out1,
  input logic [1:0]  out0,
  input logic [1:0]  mux_out
);
  default clocking cb @(posedge clk); endclocking

  // Sanity: no X/Z on primary inputs
  assert property (!$isunknown({reset,select,data_in}));

  // split_input correctness
  assert property (out2 == data_in[7:6]);
  assert property (out1 == data_in[5:4]);
  assert property (out0 == data_in[3:2]);

  // mux correctness (c/third input is unused by RTL)
  assert property (!$isunknown(select) && (select==1'b0) |-> mux_out == out0);
  assert property (!$isunknown(select) && (select==1'b1) |-> mux_out == out1);

  // Registered output behavior
  // Upper bits always zero
  assert property (final_output[7:2] == 6'b0);

  // Reset takes effect on the following cycle
  assert property ($past(reset) |-> final_output == 8'h00);

  // Normal update: mirror prior mux_out in LSBs (with zero padding)
  assert property ($past(!reset) |-> final_output == {6'b0, $past(mux_out)});

  // No X/Z on internal mux_out after reset is released
  assert property (disable iff (reset) !$isunknown(mux_out));

  // Coverage
  cover property (reset ##1 !reset);                      // reset pulse observed
  cover property (!reset && select==1'b0);                // select 0 used
  cover property (!reset && select==1'b1);                // select 1 used
  cover property (!reset && final_output[1:0]==2'b00);
  cover property (!reset && final_output[1:0]==2'b01);
  cover property (!reset && final_output[1:0]==2'b10);
  cover property (!reset && final_output[1:0]==2'b11);
endmodule

// Bind into the DUT
bind top_module top_module_sva sva_i (
  .clk(clk),
  .reset(reset),
  .data_in(data_in),
  .select(select),
  .final_output(final_output),
  .out2(out2),
  .out1(out1),
  .out0(out0),
  .mux_out(mux_out)
);