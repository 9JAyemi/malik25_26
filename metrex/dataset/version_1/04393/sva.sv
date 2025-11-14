// SVA for DFFSR: synchronous R/S with R > S priority
module DFFSR_sva(input logic C, S, R, D, Q);

  default clocking cb @(posedge C); endclocking

  // Functional next-state correctness (sample inputs at clk, check Q after NBA)
  assert property ( $past(1'b1) |-> ##0 ( Q == (R ? 1'b0 : S ? 1'b1 : $past(D)) ) );

  // R dominates S when both asserted
  assert property ( (R && S) |-> ##0 (Q == 1'b0) );

  // Q changes only on a clock rising edge
  assert property ( @(posedge Q or negedge Q) $rose(C) );

  // No X/Z on controls at clock; Q not X/Z after update
  assert property ( !$isunknown({R,S,D}) );
  assert property ( 1'b1 |-> ##0 !$isunknown(Q) );

  // Coverage
  cover property ( R );                       // reset path taken
  cover property ( S && !R );                 // set path taken
  cover property ( R && S );                  // conflict seen (priority exercised)
  cover property ( $past(1'b1) && !R && !S && D != $past(Q) ); // data-driven toggle
  cover property ( $past(1'b1) && !R && !S && D == $past(Q) ); // data-driven hold

endmodule

bind DFFSR DFFSR_sva sva_DFFSR (.*);