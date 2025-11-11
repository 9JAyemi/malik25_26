// SVA for sky130_fd_sc_lp__a32o
module sky130_fd_sc_lp__a32o_sva (input logic A1,A2,A3,B1,B2, X);

  // Reference function and immediate check (zero-delay)
  logic a_and, b_and, refX;
  always_comb begin
    a_and = A1 & A2 & A3;
    b_and = B1 & B2;
    refX  = a_and | b_and;
    assert (#0 (X === refX))
      else $error("a32o func mismatch: X=%0b ref=%0b A={%0b%0b%0b} B={%0b%0b}", X, refX, A1,A2,A3,B1,B2);
  end

  // Sample on any input/output edge
  default clocking cb @(
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge A3 or negedge A3 or
    posedge B1 or negedge B1 or
    posedge B2 or negedge B2 or
    posedge X  or negedge X
  ); endclocking

  // Functional equivalence and no-X when inputs known
  property p_func;
    disable iff ($isunknown({A1,A2,A3,B1,B2}))
      (X == ((A1 & A2 & A3) | (B1 & B2))) && !$isunknown(X);
  endproperty
  assert property (p_func);

  // No spurious output toggle without input change
  assert property ( $stable({A1,A2,A3,B1,B2}) |-> $stable(X) );

  // Functional corner coverage
  cover property ( !(A1&A2&A3) && !(B1&B2) && X==0 );
  cover property (  (A1&A2&A3) && !(B1&B2) && X==1 );
  cover property ( !(A1&A2&A3) &&  (B1&B2) && X==1 );
  cover property (  (A1&A2&A3) &&  (B1&B2) && X==1 );

  // Sensitization/toggle coverage per input (other term off so output reflects the input)
  cover property ( (A2 && A3 && !(B1&B2)) ##1 $rose(A1) ##0 $rose(X) );
  cover property ( (A2 && A3 && !(B1&B2)) ##1 $fell(A1) ##0 $fell(X) );
  cover property ( (A1 && A3 && !(B1&B2)) ##1 $rose(A2) ##0 $rose(X) );
  cover property ( (A1 && A3 && !(B1&B2)) ##1 $fell(A2) ##0 $fell(X) );
  cover property ( (A1 && A2 && !(B1&B2)) ##1 $rose(A3) ##0 $rose(X) );
  cover property ( (A1 && A2 && !(B1&B2)) ##1 $fell(A3) ##0 $fell(X) );

  cover property ( (B2 && !(A1&A2&A3)) ##1 $rose(B1) ##0 $rose(X) );
  cover property ( (B2 && !(A1&A2&A3)) ##1 $fell(B1) ##0 $fell(X) );
  cover property ( (B1 && !(A1&A2&A3)) ##1 $rose(B2) ##0 $rose(X) );
  cover property ( (B1 && !(A1&A2&A3)) ##1 $fell(B2) ##0 $fell(X) );

endmodule

bind sky130_fd_sc_lp__a32o sky130_fd_sc_lp__a32o_sva sva_inst (.*);