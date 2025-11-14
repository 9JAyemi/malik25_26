// SVA checker for simple_calc
module simple_calc_sva #(parameter int W=8)
(
  input logic [W-1:0] a,
  input logic [W-1:0] b,
  input logic         op,
  input logic [W-1:0] sum,
  input logic [W-1:0] diff
);

  // Sample on any relevant signal activity
  default clocking cb @(a or b or op or sum or diff); endclocking

  // Functional correctness (8-bit truncation of 9-bit arithmetic)
  assert property ( sum == (a + b)[W-1:0] );
  assert property ( diff == (op ? (a - b) : (b - a))[W-1:0] );

  // Sum must not depend on op
  assert property ( $changed(op) && !$changed(a) && !$changed(b) |-> $stable(sum) );

  // Outputs must be known when inputs are known
  assert property ( !$isunknown({a,b,op}) |-> !$isunknown({sum,diff}) );

  // Basic functional coverage
  cover property ( op == 1 );
  cover property ( op == 0 );
  cover property ( (a + b)[W] );                 // add overflow
  cover property ( op && (a < b) );              // a-b borrow
  cover property ( !op && (b < a) );             // b-a borrow
  cover property ( a == b && diff == '0 );       // equal operands -> zero diff
  cover property ( a == '0 && b == '0 );
  cover property ( a == '1 && b == '1 );
  cover property ( a == '0 && b == '1 );
  cover property ( a == '1 && b == '0 );
  cover property ( !$changed(a) && !$changed(b) && $changed(op) ); // op toggle case

endmodule

// Bind into DUT
bind simple_calc simple_calc_sva #(.W(8)) u_simple_calc_sva (.*);