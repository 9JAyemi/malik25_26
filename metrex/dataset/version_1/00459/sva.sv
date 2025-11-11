// SVA for sequential_circuit: 3-stage shift of 'a' to 'q' over clk
module sequential_circuit_sva (
  input clk,
  input a,
  input q,
  input q1,
  input q2
);
  default clocking cb @(posedge clk); endclocking

  // Stage-by-stage functional checks (both 0 and 1 cases)
  assert property ( a   |=> q1 );
  assert property ( !a  |=> !q1 );
  assert property ( q1  |=> q2 );
  assert property ( !q1 |=> !q2 );
  assert property ( q2  |=> q );
  assert property ( !q2 |=> !q );

  // End-to-end: a should appear at q after 3 cycles
  assert property ( a   |=> ##2 q );
  assert property ( !a  |=> ##2 !q );

  // X-propagation sanity: known input yields known next-stage
  assert property ( !$isunknown(a)  |=> !$isunknown(q1) );
  assert property ( !$isunknown(q1) |=> !$isunknown(q2) );
  assert property ( !$isunknown(q2) |=> !$isunknown(q) );
  assert property ( !$isunknown(a)  |=> ##2 !$isunknown(q) );

  // Coverage: both edges and steady values propagate through pipeline
  cover property ( $rose(a) ##1 $rose(q1) ##1 $rose(q2) ##1 $rose(q) );
  cover property ( $fell(a) ##1 $fell(q1) ##1 $fell(q2) ##1 $fell(q) );
  cover property ( a  ##1 q1  ##1 q2  ##1 q );
  cover property ( !a ##1 !q1 ##1 !q2 ##1 !q );
endmodule

bind sequential_circuit sequential_circuit_sva i_sequential_circuit_sva (
  .clk(clk), .a(a), .q(q), .q1(q1), .q2(q2)
);