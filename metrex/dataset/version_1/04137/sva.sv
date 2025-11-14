// SVA checkers for binary_adder and top_module

// Checker for binary_adder
module binary_adder_sva (binary_adder m);
  // Functional correctness and arithmetic equivalence; no X on outputs when inputs known
  assert property ( !$isunknown({m.a,m.b,m.carry_in}) |-> (
      m.sum        === (m.a ^ m.b ^ m.carry_in) &&
      m.carry_out  === ((m.a & m.b) | (m.carry_in & (m.a ^ m.b))) &&
      {m.carry_out,m.sum} === ({1'b0,m.a} + {1'b0,m.b} + {1'b0,m.carry_in})
  ));

  // Outputs can be X only if some input is X
  assert property ( $isunknown({m.sum,m.carry_out}) |-> $isunknown({m.a,m.b,m.carry_in}) );

  // Coverage: interesting points of the truth table
  cover property ( ! $isunknown({m.a,m.b,m.carry_in}) && (m.carry_in==1'b0) && m.a && m.b );     // a=b=1, cin=0
  cover property ( ! $isunknown({m.a,m.b,m.carry_in}) && (m.carry_in==1'b1) && (m.a ^ m.b) );    // a^b=1, cin=1
  cover property ( ! $isunknown({m.a,m.b,m.carry_in}) && m.sum && m.carry_out );                 // sum=1, cout=1
endmodule

bind binary_adder binary_adder_sva (.m());

// Checker for top_module
module top_module_sva (top_module m);
  // Instantiated adders should be half adders (carry_in tied low)
  assert property ( m.adder1.carry_in === 1'b0 );
  assert property ( m.adder2.carry_in === 1'b0 );

  // Internal adder signal correctness
  assert property ( !$isunknown({m.a1,m.b1}) |-> (m.sum1 === (m.a1 ^ m.b1) && m.carry1 === (m.a1 & m.b1)) );
  assert property ( !$isunknown({m.a2,m.b2}) |-> (m.sum2 === (m.a2 ^ m.b2) && m.carry2 === (m.a2 & m.b2)) );

  // Top-level sum correctness (bitwise and arithmetic forms)
  assert property ( !$isunknown({m.a1,m.b1,m.a2,m.b2,m.select}) |-> (
    m.sum[0] === ((m.a1 ^ m.b1) ^ (m.a2 ^ m.b2)) &&
    m.sum[1] === ((m.select ? (m.a2 & m.b2) : (m.a1 & m.b1)) ^ (((m.a1 ^ m.b1) & (m.a2 ^ m.b2))))
  ));
  assert property ( !$isunknown({m.a1,m.b1,m.a2,m.b2,m.select}) |-> (
    m.sum === ( { (m.select ? (m.a2 & m.b2) : (m.a1 & m.b1)), (m.a1 ^ m.b1) } + {1'b0, (m.a2 ^ m.b2)} )
  ));

  // No X on outputs when inputs are known
  assert property ( !$isunknown({m.a1,m.b1,m.a2,m.b2,m.select}) |-> ! $isunknown(m.sum) );

  // Coverage: both select paths, carries, LSB carry, and extreme sums
  cover property ( !$isunknown({m.a1,m.b1,m.a2,m.b2,m.select}) && m.select==1'b0 );
  cover property ( !$isunknown({m.a1,m.b1,m.a2,m.b2,m.select}) && m.select==1'b1 );
  cover property ( !$isunknown({m.a1,m.b1}) && m.carry1 );
  cover property ( !$isunknown({m.a2,m.b2}) && m.carry2 );
  cover property ( !$isunknown({m.a1,m.b1,m.a2,m.b2}) && (m.sum1 & m.sum2) ); // LSB carry into MSB
  cover property ( !$isunknown({m.a1,m.b1,m.a2,m.b2,m.select}) && m.sum == 2'b00 );
  cover property ( !$isunknown({m.a1,m.b1,m.a2,m.b2,m.select}) && m.sum == 2'b11 );
endmodule

bind top_module top_module_sva (.m());