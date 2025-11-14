// SVA for HAX1 (Half Adder)
// Bind this to the DUT to check functional correctness, X-handling, and basic coverage.

module HAX1_sva(input logic A, B, YC, YS);

  // Sample on any input edge
  default clocking cb @(posedge A or negedge A or posedge B or negedge B); endclocking

  // Core functional correctness (concise: both outputs at once)
  property p_add_correct;
    !$isunknown({A,B}) |-> {YC,YS} === (A + B);
  endproperty
  assert property (p_add_correct);

  // Redundant but explicit relations
  assert property (!$isunknown({A,B}) |-> (YC === (A & B)));
  assert property (!$isunknown({A,B}) |-> (YS === (A ^ B)));

  // No invalid combination when outputs are known
  assert property (!$isunknown({YC,YS}) |-> !(YC && YS));

  // X-handling sanity
  assert property (!$isunknown({A,B}) |-> !$isunknown({YC,YS}));
  assert property ( $isunknown({YC,YS}) |->  $isunknown({A,B}));

  // Outputs must not change unless some input changed (no hidden state)
  assert property (@(posedge YC or negedge YC) $changed({A,B}));
  assert property (@(posedge YS or negedge YS) $changed({A,B}));

  // Truth-table coverage
  cover property (A==0 && B==0 ##0 YC==0 && YS==0);
  cover property (A==0 && B==1 ##0 YC==0 && YS==1);
  cover property (A==1 && B==0 ##0 YC==0 && YS==1);
  cover property (A==1 && B==1 ##0 YC==1 && YS==0);

endmodule

// Bind to DUT
bind HAX1 HAX1_sva hax1_sva_i(.A(A), .B(B), .YC(YC), .YS(YS));