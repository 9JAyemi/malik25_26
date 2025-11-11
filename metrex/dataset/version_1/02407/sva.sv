// SVA for binary_max
// Checks next-cycle behavior due to NBA semantics and provides concise coverage.

module binary_max_sva (
  input logic        clk,
  input logic [3:0]  A,
  input logic [3:0]  B,
  input logic [3:0]  max,
  input logic        max_sel
);
  default clocking cb @(posedge clk); endclocking

  // After any cycle with known inputs, outputs must be known next cycle
  assert property ( !$isunknown({A,B}) |=> !$isunknown({max,max_sel}) );

  // Functional correctness (next-cycle update semantics)
  assert property ( !$isunknown({A,B}) && (A > B)  |=> (max_sel && max == A) );
  assert property ( !$isunknown({A,B}) && !(A > B) |=> (!max_sel && max == B) );

  // Consistency between selector and output data
  assert property ( !$isunknown({A,B}) |=> (max == (max_sel ? A : B)) );

  // Coverage: exercise both branches and equality tie-case
  cover property ( (A > B)  ##1 (max_sel && max == A) );
  cover property ( (A < B)  ##1 (!max_sel && max == B) );
  cover property ( (A == B) ##1 (!max_sel && max == B) );
endmodule

// Bind to DUT
bind binary_max binary_max_sva u_binary_max_sva (
  .clk(clk), .A(A), .B(B), .max(max), .max_sel(max_sel)
);