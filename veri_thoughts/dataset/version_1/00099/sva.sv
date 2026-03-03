// SVA for four_input_module
// Bind into DUT
bind four_input_module four_input_module_sva sva_inst (.A(A), .B(B), .X(X));

module four_input_module_sva (
  input logic [1:0] A,
  input logic [1:0] B,
  input logic       X
);

  // Clocking on any input change; use ##0 to allow combinational settle
  event ab_edge;  always @(A or B) -> ab_edge;
  default clocking cb @(ab_edge); endclocking

  // Functional equivalence (mask unknown inputs)
  assert property ( !$isunknown({A,B}) |-> ##0 (X === ((A[0]&A[1]) ^ (B[0]|B[1]))) );

  // Output must be known when inputs are known
  assert property ( !$isunknown({A,B}) |-> ##0 !$isunknown(X) );

  // Any X toggle must be caused by an input toggle
  assert property ( @(posedge X or negedge X) ($changed(A) || $changed(B)) );

  // Functional coverage (C1=&A, C2=|B) — all 4 regions
  cover property ( !$isunknown({A,B}) ##0 ((&A)==0 && (|B)==0) );
  cover property ( !$isunknown({A,B}) ##0 ((&A)==0 && (|B)==1) );
  cover property ( !$isunknown({A,B}) ##0 ((&A)==1 && (|B)==0) );
  cover property ( !$isunknown({A,B}) ##0 ((&A)==1 && (|B)==1) );

  // Output value and edge coverage
  cover property ( !$isunknown({A,B}) ##0 (X==0) );
  cover property ( !$isunknown({A,B}) ##0 (X==1) );
  cover property ( $rose(X) );
  cover property ( $fell(X) );

  // Optional: hit all A and B encodings
  cover property ( A==2'b00 );  cover property ( A==2'b01 );
  cover property ( A==2'b10 );  cover property ( A==2'b11 );
  cover property ( B==2'b00 );  cover property ( B==2'b01 );
  cover property ( B==2'b10 );  cover property ( B==2'b11 );

endmodule