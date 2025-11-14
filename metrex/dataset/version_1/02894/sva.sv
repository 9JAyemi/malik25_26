// SVA for xor_nand — concise, high-quality checks and coverage
module xor_nand_sva (
  input logic a,
  input logic b,
  input logic out,
  input logic nand1
);
  // Trigger on any input edge
  default clocking cb @(posedge a or negedge a or posedge b or negedge b); endclocking

  // Functional correctness (guard against X/Z on inputs)
  assert property (!$isunknown({a,b})) |-> (out === (a & b));
  assert property (!$isunknown({a,b})) |-> (nand1 === ~(a & b));
  assert property (!$isunknown(nand1)) |-> (out === ~nand1);

  // Knownness: known inputs imply known internal/output
  assert property (!$isunknown({a,b})) |-> (!$isunknown({nand1,out}));

  // Settle in the same timestep after any input change
  assert property ( ($changed(a) || $changed(b)) |->
                    ##0 ((nand1 === ~(a & b)) && (out === (a & b)) && (out === ~nand1)) );

  // Functional coverage: all input/output combinations observed
  cover property ((a==1'b0 && b==1'b0) && out==1'b0);
  cover property ((a==1'b0 && b==1'b1) && out==1'b0);
  cover property ((a==1'b1 && b==1'b0) && out==1'b0);
  cover property ((a==1'b1 && b==1'b1) && out==1'b1);

  // Transition coverage: output reacts correctly to single-input toggles
  cover property ( b && $rose(a) ##0 $rose(out));
  cover property ( b && $fell(a) ##0 $fell(out));
  cover property ( a && $rose(b) ##0 $rose(out));
  cover property ( a && $fell(b) ##0 $fell(out));
endmodule

// Bind into the DUT (accesses internal wire nand1)
bind xor_nand xor_nand_sva sva(.a(a), .b(b), .out(out), .nand1(nand1));