// SVA for four_input_gate
// Bind this module to the DUT and provide a clock/reset from your TB.

module four_input_gate_sva (
  input logic clk,
  input logic rst_n,
  input logic A1, A2, B1, B2,
  input logic X
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Helper predicates
  function automatic logic pairs_or;
    return ((A1 & A2) | (B1 & B2));
  endfunction

  function automatic logic all_four_ones;
    return (A1 & A2 & B1 & B2);
  endfunction

  function automatic logic known_inputs;
    return !$isunknown({A1,A2,B1,B2});
  endfunction

  // Core functional equivalence (on known inputs)
  assert property ( known_inputs() |-> X == (pairs_or() & !all_four_ones()) )
    else $error("four_input_gate: X mismatch");

  // Output never X when inputs are known
  assert property ( known_inputs() |-> !$isunknown(X) )
    else $error("four_input_gate: X is X/Z on known inputs");

  // Key corner cases
  assert property ( all_four_ones() |-> X == 1'b0 )
    else $error("four_input_gate: 1111 must produce 0");

  assert property ( known_inputs() && (A1 & A2) && !(B1 & B2) |-> X == 1'b1 )
    else $error("four_input_gate: A-pair-only must produce 1");

  assert property ( known_inputs() && (B1 & B2) && !(A1 & A2) |-> X == 1'b1 )
    else $error("four_input_gate: B-pair-only must produce 1");

  assert property ( known_inputs() && !(A1 & A2) && !(B1 & B2) |-> X == 1'b0 )
    else $error("four_input_gate: no-pair must produce 0");

  // Toggle coverage
  cover property ($rose(X));
  cover property ($fell(X));

  // Full input-space coverage (16 combinations)
  cover property ({A1,A2,B1,B2} == 4'b0000);
  cover property ({A1,A2,B1,B2} == 4'b0001);
  cover property ({A1,A2,B1,B2} == 4'b0010);
  cover property ({A1,A2,B1,B2} == 4'b0011);
  cover property ({A1,A2,B1,B2} == 4'b0100);
  cover property ({A1,A2,B1,B2} == 4'b0101);
  cover property ({A1,A2,B1,B2} == 4'b0110);
  cover property ({A1,A2,B1,B2} == 4'b0111);
  cover property ({A1,A2,B1,B2} == 4'b1000);
  cover property ({A1,A2,B1,B2} == 4'b1001);
  cover property ({A1,A2,B1,B2} == 4'b1010);
  cover property ({A1,A2,B1,B2} == 4'b1011);
  cover property ({A1,A2,B1,B2} == 4'b1100);
  cover property ({A1,A2,B1,B2} == 4'b1101);
  cover property ({A1,A2,B1,B2} == 4'b1110);
  cover property ({A1,A2,B1,B2} == 4'b1111);

  // Cover expected output for representative classes
  cover property ( (A1 & A2) && !(B1 & B2) && X );
  cover property ( (B1 & B2) && !(A1 & A2) && X );
  cover property ( !(A1 & A2) && !(B1 & B2) && !X );
  cover property ( all_four_ones() && !X );

endmodule

// Example bind (edit clk/rst paths to your TB)
// bind four_input_gate four_input_gate_sva u_four_input_gate_sva ( .clk(tb.clk), .rst_n(tb.rst_n), .A1(A1), .A2(A2), .B1(B1), .B2(B2), .X(X) );