// SVA for selem: concise, full functional checks + key coverage
module selem_sva (
  input logic sreq_0n,
  input logic sreq_1n,
  input logic activateOut_0r,
  input logic activateOut_0a
);
  default clocking cb @(*); endclocking

  // Functional correctness (guarded against X on inputs; ##0 to avoid race)
  assert property ( !$isunknown({sreq_0n,sreq_1n}) |-> ##0 (activateOut_0r == (sreq_0n & sreq_1n)) );
  assert property ( !$isunknown({sreq_0n,sreq_1n}) |-> ##0 (activateOut_0a == (sreq_0n | sreq_1n)) );

  // Knownness behavior
  assert property ( !$isunknown({sreq_0n,sreq_1n}) |-> ##0 !$isunknown({activateOut_0r,activateOut_0a}) );
  assert property ( $isunknown(activateOut_0r) |-> ($isunknown(sreq_0n) || $isunknown(sreq_1n)) );
  assert property ( $isunknown(activateOut_0a) |-> ($isunknown(sreq_0n) || $isunknown(sreq_1n)) );

  // No spurious glitches: outputs stable when inputs stable
  assert property ( $stable({sreq_0n,sreq_1n}) |-> ##0 $stable({activateOut_0r,activateOut_0a}) );

  // Output changes must be driven by input changes
  assert property ( $changed({activateOut_0r,activateOut_0a}) |-> ($changed(sreq_0n) || $changed(sreq_1n)) );

  // Cross-relation: AND implies OR (when outputs known)
  assert property ( !$isunknown({activateOut_0r,activateOut_0a}) |-> ##0 (!activateOut_0r || activateOut_0a) );

  // Functional coverage: all input/output truth-table points observed
  cover property ( (sreq_0n==0 && sreq_1n==0) ##0 (activateOut_0r==0 && activateOut_0a==0) );
  cover property ( (sreq_0n==0 && sreq_1n==1) ##0 (activateOut_0r==0 && activateOut_0a==1) );
  cover property ( (sreq_0n==1 && sreq_1n==0) ##0 (activateOut_0r==0 && activateOut_0a==1) );
  cover property ( (sreq_0n==1 && sreq_1n==1) ##0 (activateOut_0r==1 && activateOut_0a==1) );

  // Output toggle coverage
  cover property ( $rose(activateOut_0r) );
  cover property ( $fell(activateOut_0r) );
  cover property ( $rose(activateOut_0a) );
  cover property ( $fell(activateOut_0a) );
endmodule

// Bind into DUT
bind selem selem_sva sva_selem (
  .sreq_0n(sreq_0n),
  .sreq_1n(sreq_1n),
  .activateOut_0r(activateOut_0r),
  .activateOut_0a(activateOut_0a)
);