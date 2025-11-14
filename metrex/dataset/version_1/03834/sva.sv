// SVA for sky130_fd_sc_ms__xnor3
// Bind to every instance and check functionality, buffering, and coverage.

module sky130_fd_sc_ms__xnor3_sva (
  input logic A, B, C, X,
  input logic xnor0_out_X
);

  // Functional correctness when inputs are known (no X/Z)
  // Output must be known and match ~(A^B^C)
  property p_func_known;
    !$isunknown({A,B,C}) |-> (!$isunknown(X) && (X == ~(A ^ B ^ C)));
  endproperty
  assert property (p_func_known)
    else $error("XNOR3 functional mismatch with known inputs");

  // Buffer integrity: X must mirror internal xnor output
  assert property (X === xnor0_out_X)
    else $error("Buffer mismatch: X != xnor0_out_X");

  // Parity-change behavior in same timestep:
  // X toggles iff an odd number of inputs toggle simultaneously.
  property p_toggle_parity;
    ($changed(X)) <-> ( $onehot({$changed(A),$changed(B),$changed(C)}) ||
                        ($changed(A) && $changed(B) && $changed(C)) );
  endproperty
  assert property (p_toggle_parity)
    else $error("XNOR3 toggle parity violation");

  // X should not be X/Z when inputs are 0/1
  assert property (!$isunknown({A,B,C}) |-> !$isunknown(X))
    else $error("Output X unknown with known inputs");

  // Basic functional equivalence sampling on any input change
  assert property ( $changed({A,B,C}) |-> ( !$isunknown({A,B,C}) && (X == ~(A ^ B ^ C)) ) )
    else $error("XNOR3 mismatch on input change");

  // Coverage: exercise all input combinations
  cover property ( {A,B,C} == 3'b000 );
  cover property ( {A,B,C} == 3'b001 );
  cover property ( {A,B,C} == 3'b010 );
  cover property ( {A,B,C} == 3'b011 );
  cover property ( {A,B,C} == 3'b100 );
  cover property ( {A,B,C} == 3'b101 );
  cover property ( {A,B,C} == 3'b110 );
  cover property ( {A,B,C} == 3'b111 );

  // Coverage: each input and output rises/falls at least once
  cover property ( $rose(A) );  cover property ( $fell(A) );
  cover property ( $rose(B) );  cover property ( $fell(B) );
  cover property ( $rose(C) );  cover property ( $fell(C) );
  cover property ( $rose(X) );  cover property ( $fell(X) );

  // Coverage: one-hot, two-hot, three-hot simultaneous input changes
  cover property ( $onehot({$changed(A),$changed(B),$changed(C)}) );
  cover property ( ($changed(A) && $changed(B) && !$changed(C)) ||
                   ($changed(A) && !$changed(B) && $changed(C)) ||
                   (!$changed(A) && $changed(B) && $changed(C)) );
  cover property ( $changed(A) && $changed(B) && $changed(C) );

endmodule

bind sky130_fd_sc_ms__xnor3 sky130_fd_sc_ms__xnor3_sva
  sva_i ( .A(A), .B(B), .C(C), .X(X), .xnor0_out_X(xnor0_out_X) );