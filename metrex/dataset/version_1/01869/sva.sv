// SVA for switch_reader
// Quality-focused, concise checks + essential coverage

module switch_reader_sva (
  input clk,
  input reset_n,
  input [3:0] switches,
  input [3:0] data_out
);
  default clocking cb @(posedge clk); endclocking

  // Reset must force output to zero whenever asserted
  assert property (!reset_n |-> (data_out == 4'd0 && !$isunknown(data_out)));

  // 1-cycle register behavior once out of reset
  assert property ((reset_n && $past(reset_n)) |-> (data_out == $past(switches)));

  // First cycle after reset release captures current switches
  assert property ($rose(reset_n) |=> (data_out == $past(switches)));

  // No X on output if prior sampled input was known and in run mode
  assert property ((reset_n && $past(reset_n) && !$isunknown($past(switches))) |-> !$isunknown(data_out));

  // Coverage: reset sequence
  cover property (!reset_n ##1 $rose(reset_n));

  // Coverage: a change on switches is reflected next cycle on data_out
  cover property ((reset_n && $past(reset_n) && switches != $past(switches)) |=> (data_out == $past(switches)));

  // Per-bit coverage of capture on change
  genvar i;
  generate for (i=0; i<4; i++) begin : COV_PER_BIT
    cover property ((reset_n && $past(reset_n) && $changed(switches[i])) |=> (data_out[i] == $past(switches[i])));
  end endgenerate
endmodule

bind switch_reader switch_reader_sva sva_inst (
  .clk(clk),
  .reset_n(reset_n),
  .switches(switches),
  .data_out(data_out)
);