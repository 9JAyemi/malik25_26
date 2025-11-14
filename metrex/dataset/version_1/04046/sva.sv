// SVA for xor_2input_nand (functionally implements XNOR)
// Bind this to the DUT to check internal NAND structure and overall function.

module xor_2input_nand_sva (
  input logic a, b,
  input logic y,
  input logic w1, w2, w3, w4
);
  // Sample on any edge of signals to avoid missing events; use ##0 to avoid NBA races.
  default clocking cb @(
    posedge a or negedge a or
    posedge b or negedge b or
    posedge w1 or negedge w1 or
    posedge w2 or negedge w2 or
    posedge w3 or negedge w3 or
    posedge w4 or negedge w4 or
    posedge y  or negedge y
  ); endclocking

  // No X/Z anywhere
  assert property (!$isunknown({a,b,w1,w2,w3,w4,y})); 

  // Internal NAND structure correctness
  assert property (##0 w1 === ~(a & b));
  assert property (##0 w2 === ~(a & w1));
  assert property (##0 w3 === ~(b & w1));
  assert property (##0 w4 === ~(w2 & w3));

  // Output relation and overall function (XNOR)
  assert property (##0 y  === ~w4);
  assert property (##0 y  === ~(a ^ b));

  // Output changes only when at least one input changes
  assert property ($changed(y) |-> ($changed(a) || $changed(b)));

  // Functional coverage: all input/output combinations and key transitions
  cover property (a==0 && b==0 && y==1);
  cover property (a==0 && b==1 && y==0);
  cover property (a==1 && b==0 && y==0);
  cover property (a==1 && b==1 && y==1);

  // Transition coverage: one-input toggle flips y; simultaneous toggle holds y
  cover property (($changed(a) ^ $changed(b)) ##0 $changed(y));
  cover property (($changed(a) && $changed(b)) ##0 !$changed(y));
endmodule

bind xor_2input_nand xor_2input_nand_sva sva_i (
  .a(a), .b(b), .y(y), .w1(w1), .w2(w2), .w3(w3), .w4(w4)
);