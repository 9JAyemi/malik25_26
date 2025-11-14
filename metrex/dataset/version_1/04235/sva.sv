// SVA for my_module
// Bind this checker to the DUT
bind my_module my_module_sva my_module_sva_inst();

module my_module_sva;

  // Access DUT scope signals directly (portless bind)
  // Clocking
  default clocking cb @(posedge clk); endclocking

  // Track valid past
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Core: outputs are 1-cycle registered versions of d[3:0]
  assert property (past_valid |-> {out3,out2,out1,out0} == $past({d3,d2,d1,d0}));

  // No X on used datapath at sample edges
  assert property (past_valid |-> !$isunknown({d3,d2,d1,d0,out3,out2,out1,out0}));

  // Combinational mux correctness for internal nets
  assert property (n2 == (d0 ? in0 : in1));
  assert property (n4 == (d3 ? in2 : in3));

  // When reset is asserted, the self-fed nets resolve to 0
  assert property (reset |-> (n1 == 1'b0 && n3 == 1'b0));

  // If mux inputs are known, mux outputs must be known
  assert property (!$isunknown({d0,in0,in1}) |-> !$isunknown(n2));
  assert property (!$isunknown({d3,in2,in3}) |-> !$isunknown(n4));

  // Covers: output edges follow input edges
  cover property (past_valid && $rose(d0) ##1 $rose(out0));
  cover property (past_valid && $fell(d0) ##1 $fell(out0));
  cover property (past_valid && $rose(d1) ##1 $rose(out1));
  cover property (past_valid && $fell(d1) ##1 $fell(out1));
  cover property (past_valid && $rose(d2) ##1 $rose(out2));
  cover property (past_valid && $fell(d2) ##1 $fell(out2));
  cover property (past_valid && $rose(d3) ##1 $rose(out3));
  cover property (past_valid && $fell(d3) ##1 $fell(out3));

  // Covers: exercise both mux select sides
  cover property (!d0 && n2 == in1);
  cover property ( d0 && n2 == in0);
  cover property (!d3 && n4 == in3);
  cover property ( d3 && n4 == in2);

  // Cover: reset drives the self-fed nets low
  cover property (reset && n1 == 1'b0 && n3 == 1'b0);

endmodule