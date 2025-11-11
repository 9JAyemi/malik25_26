// SVA for mux4: bind into DUT scope so we can see internal nets
bind mux4 mux4_sva();

module mux4_sva;

  default clocking cb @ (posedge $global_clock); endclocking

  // Functional equivalence
  assert property ( x === ((~s1 & ~s0 & a0) | (~s1 & s0 & a1) | (s1 & ~s0 & a2) | (s1 & s0 & a3)) );

  // Structural checks
  assert property ( not_s0 === ~s0 );
  assert property ( not_s1 === ~s1 );
  assert property ( and1   === (a0 & not_s1 & not_s0) );
  assert property ( and2   === (a1 & not_s1 & s0) );
  assert property ( and3   === (a2 & s1 & not_s0) );
  assert property ( and4   === (a3 & s1 & s0) );
  assert property ( or1    === (and1 | and2) );
  assert property ( or2    === (and3 | and4) );
  assert property ( x      === (or1 | or2) );

  // Decode sanity: exactly one select term high when selects are known
  assert property ( !$isunknown({s1,s0}) |-> $onehot({~s1 & ~s0, ~s1 & s0, s1 & ~s0, s1 & s0}) );
  // At most one AND-path active when selects are known
  assert property ( !$isunknown({s1,s0}) |-> $onehot0({and1,and2,and3,and4}) );

  // No X on output when all inputs known
  assert property ( !$isunknown({a0,a1,a2,a3,s0,s1}) |-> !$isunknown(x) );

  // Per-select pass-through (explicit, debuggable)
  assert property ( !$isunknown({s1,s0,a0}) && {s1,s0}==2'b00 |-> x===a0 );
  assert property ( !$isunknown({s1,s0,a1}) && {s1,s0}==2'b01 |-> x===a1 );
  assert property ( !$isunknown({s1,s0,a2}) && {s1,s0}==2'b10 |-> x===a2 );
  assert property ( !$isunknown({s1,s0,a3}) && {s1,s0}==2'b11 |-> x===a3 );

  // Coverage: exercise all selects and both output values per select
  cover property ( !$isunknown({s1,s0}) && {s1,s0}==2'b00 );
  cover property ( !$isunknown({s1,s0}) && {s1,s0}==2'b01 );
  cover property ( !$isunknown({s1,s0}) && {s1,s0}==2'b10 );
  cover property ( !$isunknown({s1,s0}) && {s1,s0}==2'b11 );

  cover property ( !$isunknown({s1,s0,a0}) && {s1,s0}==2'b00 && a0==1'b0 && x==1'b0 );
  cover property ( !$isunknown({s1,s0,a0}) && {s1,s0}==2'b00 && a0==1'b1 && x==1'b1 );
  cover property ( !$isunknown({s1,s0,a1}) && {s1,s0}==2'b01 && a1==1'b0 && x==1'b0 );
  cover property ( !$isunknown({s1,s0,a1}) && {s1,s0}==2'b01 && a1==1'b1 && x==1'b1 );
  cover property ( !$isunknown({s1,s0,a2}) && {s1,s0}==2'b10 && a2==1'b0 && x==1'b0 );
  cover property ( !$isunknown({s1,s0,a2}) && {s1,s0}==2'b10 && a2==1'b1 && x==1'b1 );
  cover property ( !$isunknown({s1,s0,a3}) && {s1,s0}==2'b11 && a3==1'b0 && x==1'b0 );
  cover property ( !$isunknown({s1,s0,a3}) && {s1,s0}==2'b11 && a3==1'b1 && x==1'b1 );

endmodule