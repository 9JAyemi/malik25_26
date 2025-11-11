// SVA for the given DUT. Bind these to the RTL for checking and coverage.

// and_using_nand: functionally implements OR of bits (out == a_b[0] | a_b[1])
module and_using_nand_sva(input logic [1:0] a_b, input logic out);
  // No Xs and functional equivalence
  always_comb begin
    assert (!$isunknown({a_b,out}));
    assert (out === (a_b[0] | a_b[1])) else $error("and_using_nand out != (a|b)");
  end
  // Truth-table coverage
  cover property (@(a_b) (a_b==2'b00) && (out==1'b0));
  cover property (@(a_b) (a_b==2'b01) && (out==1'b1));
  cover property (@(a_b) (a_b==2'b10) && (out==1'b1));
  cover property (@(a_b) (a_b==2'b11) && (out==1'b1));
  // Toggle coverage
  cover property (@(posedge out) 1);
  cover property (@(negedge out) 1);
endmodule

// dff_with_reset: synchronous reset; q updates from d on clk posedge
module dff_with_reset_sva(input logic clk, reset, d, q);
  default clocking cb @(posedge clk); endclocking
  // No Xs on sampled controls/data
  assert property (!$isunknown({reset,d}));
  // Reset dominates
  assert property (reset |=> ##0 (q==1'b0));
  // Capture d when not reset
  assert property (!reset |=> ##0 (q == $sampled(d)));
  // q changes only on clk posedge
  always @(q) assert ($rose(clk)) else $error("q changed without clk posedge");
  // Coverage
  cover property (reset |=> ##0 (q==0));
  cover property (!reset && $sampled(d) |=> ##0 (q==1));
  cover property (!reset && !$sampled(d) |=> ##0 (q==0));
endmodule

// functional_module: clocks on and_out; q mirrors dff_out at that edge
module functional_module_sva(input logic and_out, dff_out, q);
  default clocking cb @(posedge and_out); endclocking
  // No Xs at clocking edge
  assert property (!$isunknown({and_out,dff_out}));
  // Functional: q updates to sampled dff_out on and_out posedge
  assert property (1 |=> ##0 (q == $sampled(dff_out)));
  // q changes only on and_out posedge
  always @(q) assert ($rose(and_out)) else $error("q changed without and_out posedge");
  // Coverage
  cover property ($sampled(dff_out) |=> ##0 (q==1));
  cover property (!$sampled(dff_out) |=> ##0 (q==0));
  cover property (@(posedge and_out) 1);
  cover property (@(negedge and_out) 1);
endmodule

// Top-level cross-checks and end-to-end behavior
module top_module_sva(
  input logic clk, reset,
  input logic [1:0] a_b,
  input logic d,
  input logic and_out, dff_out, q
);
  // Mirror check: and_out equals (a_b[0]|a_b[1])
  assert property (@(a_b or and_out) and_out === (a_b[0] | a_b[1]));
  // End-to-end: on and_out edge, q reflects dff_out
  assert property (@(posedge and_out) 1 |=> ##0 (q == $sampled(dff_out)));
  // CDC-related coverage: both sampling outcomes
  cover property (@(posedge and_out) dff_out |=> ##0 q);
  cover property (@(posedge and_out) !dff_out |=> ##0 !q);
  // Coincidence coverage (edge alignment)
  cover property (@(posedge and_out) $rose(clk));
endmodule

// Bind SVA to DUT
bind and_using_nand   and_using_nand_sva    i_and_using_nand_sva   (.a_b(a_b), .out(out));
bind dff_with_reset   dff_with_reset_sva    i_dff_with_reset_sva   (.clk(clk), .reset(reset), .d(d), .q(q));
bind functional_module functional_module_sva i_functional_module_sva(.and_out(and_out), .dff_out(dff_out), .q(q));
bind top_module       top_module_sva        i_top_module_sva       (.clk(clk), .reset(reset), .a_b(a_b), .d(d),
                                                                   .and_out(and_out), .dff_out(dff_out), .q(q));