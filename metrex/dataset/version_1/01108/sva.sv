// SVA for top_module. Bind into DUT for checking and coverage.
module top_module_sva (top_module dut);
  default clocking cb @(posedge dut.clk); endclocking

  // Combinational correctness
  assert property (dut.adder_sum == (dut.a + dut.b));
  assert property (dut.min_value == 8'h00);
  assert property (dut.product == {dut.adder_sum, dut.min_value});
  assert property (dut.product[15:8] == dut.adder_sum && dut.product[7:0] == dut.min_value);

  // Sequential register updates (one-cycle latency from sampled inputs)
  assert property (!dut.reset && $past(!dut.reset) |->
                   dut.sum == ($past(dut.select) ? $past(dut.adder_sum) : $past(dut.min_value)) &&
                   dut.min == ($past(dut.select) ? $past(dut.min_value) : $past(dut.adder_sum)));

  // Reset behavior
  assert property (dut.reset |=> (dut.sum == 8'h00 && dut.min == 8'h00));
  assert property (dut.reset && $past(dut.reset) |-> (dut.sum == 8'h00 && dut.min == 8'h00));

  // No X on architectural outputs in normal operation
  assert property (!dut.reset && $past(!dut.reset) |->
                   !$isunknown({dut.sum, dut.min, dut.product}));

  // Useful coverage
  cover property (!dut.reset && $past(!dut.reset) && $past(dut.select) ##1
                  (dut.sum == $past(dut.adder_sum) && dut.min == $past(dut.min_value)));
  cover property (!dut.reset && $past(!dut.reset) && !$past(dut.select) ##1
                  (dut.sum == $past(dut.min_value) && dut.min == $past(dut.adder_sum)));
  // Addition wrap-around seen
  cover property (!dut.reset && $past(!dut.reset) &&
                  $past(({1'b0,dut.a}+{1'b0,dut.b})[8]));
endmodule

bind top_module top_module_sva sva_top_module_i(.dut());