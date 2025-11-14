// SVA for adder4 and full_adder
// Bind these into the DUT to check functionality and provide concise coverage.

module adder4_sva;
  // Bound inside adder4; has visibility to A,B,O,C,sum,carry1..carry3
  default clocking cb @(*); endclocking

  // End-to-end correctness
  assert property ({C,O} == A + B);

  // Stage-wise ripple correctness
  assert property ({carry1, sum[0]} == A[0] + B[0]);
  assert property ({carry2, sum[1]} == A[1] + B[1] + carry1);
  assert property ({carry3, sum[2]} == A[2] + B[2] + carry2);
  assert property ({C,     sum[3]} == A[3] + B[3] + carry3);

  // Structural consistency
  assert property (O == sum);

  // X-propagation guard
  assert property (!$isunknown({A,B}) |-> !$isunknown({sum,carry1,carry2,carry3,O,C}));

  // Compact functional coverage
  cover property (C);                         // overflow seen
  cover property ({carry1,carry2,carry3} == 3'b111); // long ripple path exercised
  cover property ({C,O} == 5'd0);             // zero + zero
  cover property ({C,O} == 5'd30);            // max (15+15)
endmodule

module full_adder_sva;
  // Bound inside full_adder; has visibility to A,B,Cin,S,Cout
  default clocking cb @(*); endclocking

  // Truth correctness
  assert property ({Cout, S} == A + B + Cin);

  // X-propagation guard
  assert property (!$isunknown({A,B,Cin}) |-> !$isunknown({S,Cout}));

  // Simple activity coverage
  cover property (S);
  cover property (Cout);
endmodule

// Bind statements
bind adder4     adder4_sva     adder4_sva_i();
bind full_adder full_adder_sva full_adder_sva_i();