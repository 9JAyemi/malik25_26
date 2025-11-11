// SVA for nor_using_nand_pipeline
// Bind these assertions to the DUT instance

module nor_using_nand_pipeline_sva(input logic clk, input logic a, b, out);
  default clocking cb @(posedge clk); endclocking

  // Track past-valid for $past usage
  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Structural correctness of each NAND stage
  assert property (nand1_out == ~(a & b));
  assert property (nand2_out == ~(a_reg & nand1_out));
  assert property (nand3_out == ~(b_reg & nand2_out));

  // Flop sampling (1-cycle latency from inputs to regs)
  assert property (past_valid |-> (a_reg == $past(a)));
  assert property (past_valid |-> (b_reg == $past(b)));

  // Implemented end-to-end function: out depends only on b (out == ~b)
  assert property (out == ~b);

  // Output independence from a (with b stable)
  assert property ($changed(a) && $stable(b) |-> $stable(out));

  // X-propagation/known-ness checks
  assert property (!$isunknown(b) |-> (!$isunknown(out) && out == ~b));
  assert property (!$isunknown({a,b}) |-> !$isunknown({nand1_out,nand2_out,nand3_out,out}));

  // Simple sanity: out equals final stage
  assert property (out == nand3_out);

  // Coverage: exercise all input combos and key transitions
  cover property ({a,b} == 2'b00);
  cover property ({a,b} == 2'b01);
  cover property ({a,b} == 2'b10);
  cover property ({a,b} == 2'b11);
  cover property ($rose(b) && $fell(out));
  cover property ($fell(b) && $rose(out));
  cover property ($changed(a) && $stable(b)); // a wiggles while b stable
endmodule

bind nor_using_nand_pipeline nor_using_nand_pipeline_sva sva(.clk(clk), .a(a), .b(b), .out(out));