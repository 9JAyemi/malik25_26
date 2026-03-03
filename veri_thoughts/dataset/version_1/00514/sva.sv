// SVA for sky130_fd_sc_lp__fa
// Bind into the DUT to check functionality, X-cleanliness, and provide compact coverage.

module sky130_fd_sc_lp__fa_sva;
  default clocking cb @(*); endclocking

  // Helper: all I/O known
  let known_io = !$isunknown({A,B,CIN,COUT,SUM});

  // Functional correctness (2-bit sum) and no-X on outputs when inputs are known
  property p_func;
    !$isunknown({A,B,CIN}) |->
      (! $isunknown({COUT,SUM}) &&
       {COUT,SUM} == ({1'b0,A} + {1'b0,B} + {1'b0,CIN}) &&
       (SUM == (A ^ B ^ CIN)));
  endproperty
  assert property (p_func);

  // Outputs become X only if some input is X
  assert property ( $isunknown({COUT,SUM}) |-> $isunknown({A,B,CIN}) );

  // Internal net consistency (lightweight structural checks)
  assert property ( or0_out      == (CIN | B) );
  assert property ( and0_out     == (or0_out & A) );
  assert property ( and1_out     == (B & CIN) );
  assert property ( or1_out_COUT == (and1_out | and0_out) );
  assert property ( COUT         == or1_out_COUT );
  assert property ( and2_out     == (CIN & A & B) );
  assert property ( nor0_out     == ~(A | or0_out) );
  assert property ( nor1_out     == ~(nor0_out | COUT) );
  assert property ( or2_out_SUM  == (nor1_out | and2_out) );
  assert property ( SUM          == or2_out_SUM );

  // Full input-space coverage (8 cases) with expected outputs
  cover property ( known_io && !A && !B && !CIN && COUT==1'b0 && SUM==1'b0 );
  cover property ( known_io && !A && !B &&  CIN && COUT==1'b0 && SUM==1'b1 );
  cover property ( known_io && !A &&  B && !CIN && COUT==1'b0 && SUM==1'b1 );
  cover property ( known_io && !A &&  B &&  CIN && COUT==1'b1 && SUM==1'b0 );
  cover property ( known_io &&  A && !B && !CIN && COUT==1'b0 && SUM==1'b1 );
  cover property ( known_io &&  A && !B &&  CIN && COUT==1'b1 && SUM==1'b0 );
  cover property ( known_io &&  A &&  B && !CIN && COUT==1'b1 && SUM==1'b0 );
  cover property ( known_io &&  A &&  B &&  CIN && COUT==1'b1 && SUM==1'b1 );

  // Carry generate/propagate/kill scenarios
  cover property ( known_io && (A & B)           && COUT==1'b1 ); // generate
  cover property ( known_io && !(A|B)            && COUT==1'b0 ); // kill
  cover property ( known_io && (A ^ B) && !CIN && COUT==1'b0 && SUM==1'b1 ); // propagate 0
  cover property ( known_io && (A ^ B) &&  CIN && COUT==1'b1 && SUM==1'b0 ); // propagate 1
endmodule

bind sky130_fd_sc_lp__fa sky130_fd_sc_lp__fa_sva sva_inst();