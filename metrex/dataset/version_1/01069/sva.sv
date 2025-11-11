// SVA checker for mux_2to1
module mux_2to1_sva;

  // Sample on any input or internal net transition
  default clocking cb @(
      posedge A or negedge A or
      posedge B or negedge B or
      posedge Sel or negedge Sel or
      posedge and_out or negedge and_out or
      posedge or_out or negedge or_out
  ); endclocking

  // Functional correctness (when inputs are known)
  property p_func;
    ! $isunknown({A,B,Sel}) |-> (Y == (Sel ? A : B));
  endproperty
  assert property (p_func);

  // Internal gate equivalence (when operands are known)
  assert property ( ! $isunknown({A,Sel})     |-> (and_out == (A & Sel)) );
  assert property ( ! $isunknown({B,and_out}) |-> (or_out  == (B | and_out)) );
  assert property ( ! $isunknown(or_out)      |-> (Y == or_out) );

  // No X on outputs when inputs are 2-state
  assert property ( ! $isunknown({A,B,Sel}) |-> ! $isunknown({and_out,or_out,Y}) );

  // Select change behavior
  assert property ( ! $isunknown({A,B}) && $changed(Sel) && (A != B) |-> ##0 $changed(Y) );
  assert property ( ! $isunknown({A,B}) && $changed(Sel) && (A == B) |-> ##0 ! $changed(Y) );

  // Functional coverage: each data path and value
  cover property ( ! $isunknown({A,B,Sel}) && (Sel==0) && (B==0) && (Y==0) );
  cover property ( ! $isunknown({A,B,Sel}) && (Sel==0) && (B==1) && (Y==1) );
  cover property ( ! $isunknown({A,B,Sel}) && (Sel==1) && (A==0) && (Y==0) );
  cover property ( ! $isunknown({A,B,Sel}) && (Sel==1) && (A==1) && (Y==1) );

  // Coverage: exercise both paths via select toggle when A!=B
  cover property ( ! $isunknown({A,B}) && (A!=B) && $changed(Sel) && $changed(Y) );

  // Coverage: internal and output toggles
  cover property ( $changed(and_out) );
  cover property ( $changed(or_out) );
  cover property ( $changed(Y) );

endmodule

// Bind the checker to all mux_2to1 instances
bind mux_2to1 mux_2to1_sva u_mux_2to1_sva();