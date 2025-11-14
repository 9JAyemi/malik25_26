// SVA for pipeline_module: 1-cycle pipeline of inverted input

module pipeline_module_sva;
  // Bound into pipeline_module scope; unqualified names refer to DUT signals
  default clocking @(posedge clk); endclocking

  // Track availability of 1-cycle $past()
  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  // Combinational correctness
  a_inv_func:    assert property (inv_in === ~in);
  a_out_mapping: assert property (out    === inv_out);

  // Pipeline behavior: out equals inverted input from previous cycle
  a_latency_func: assert property (past_valid |-> out === ~ $past(in));

  // X-propagation sanity: known input yields known inverted wire/output
  a_no_x_inv_in:  assert property (!$isunknown(in)          |-> !$isunknown(inv_in));
  a_no_x_out:     assert property (past_valid && !$isunknown($past(in)) |-> !$isunknown(out));

  // Functional coverage
  c_rise_then_out0: cover property (past_valid && $rose(in) ##1 out == 1'b0);
  c_fall_then_out1: cover property (past_valid && $fell(in) ##1 out == 1'b1);
  c_hold0_maps1:    cover property (past_valid && in == 1'b0 ##1 out == 1'b1);
  c_hold1_maps0:    cover property (past_valid && in == 1'b1 ##1 out == 1'b0);
endmodule

bind pipeline_module pipeline_module_sva sva_inst();