// SVA checkers and binds for and_or_gate and top_module

// Checker for the combinational and_or_gate (bind inside to see intermediates)
module and_or_gate_sva(
  input logic a,
  input logic b,
  input logic out,
  input logic intermediate1,
  input logic intermediate2
);
  // Sample on any edge of inputs to catch all combinational changes
  default clocking cb @(posedge a or negedge a or posedge b or negedge b); endclocking

  // Functional equivalence
  assert property (out === (a & b));

  // Internal consistency/redundancy
  assert property (intermediate1 === (a & b));
  assert property (intermediate2 === (a & b));
  assert property (intermediate1 === intermediate2);
  assert property (out === (intermediate1 | intermediate2));
  assert property (out === intermediate1);
  assert property (out === intermediate2);

  // Basic functional coverage: all input combos and output toggles
  cover property (a==0 && b==0);
  cover property (a==0 && b==1);
  cover property (a==1 && b==0);
  cover property (a==1 && b==1);
  cover property ($rose(out));
  cover property ($fell(out));
endmodule

bind and_or_gate and_or_gate_sva u_and_or_gate_sva(
  .a(a), .b(b), .out(out),
  .intermediate1(intermediate1),
  .intermediate2(intermediate2)
);

// Checker for the sequential top_module (bind to see internal and_or_out)
module top_module_sva(
  input logic clk,
  input logic a,
  input logic b,
  input logic out_always_ff,
  input logic and_or_out
);
  default clocking cb @(posedge clk); endclocking

  // Registering behavior: sample guards avoid first-cycle $past unknown
  assert property ($past(1'b1) |-> (out_always_ff === $past(and_or_out)));
  assert property ($past(1'b1) |-> (out_always_ff === $past(a & b)));

  // X-propagation sanity
  assert property (!$isunknown({a,b}) |-> !$isunknown(and_or_out));
  assert property ($past(!$isunknown({a,b})) |-> !$isunknown(out_always_ff));

  // Coverage: observe each input combo and expected next-cycle output
  cover property ((a==0 && b==0) ##1 (out_always_ff==0));
  cover property ((a==0 && b==1) ##1 (out_always_ff==0));
  cover property ((a==1 && b==0) ##1 (out_always_ff==0));
  cover property ((a==1 && b==1) ##1 (out_always_ff==1));

  // Output toggles
  cover property ($rose(out_always_ff));
  cover property ($fell(out_always_ff));
endmodule

bind top_module top_module_sva u_top_module_sva(
  .clk(clk), .a(a), .b(b), .out_always_ff(out_always_ff), .and_or_out(and_or_out)
);