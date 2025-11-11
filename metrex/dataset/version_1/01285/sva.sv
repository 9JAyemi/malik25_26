// SVA for mux4to1. Bind these to the DUT.
// Sampling on any input toggle to check combinational behavior reliably.

module mux4to1_sva;

  // Use DUT scope signals directly (via bind)
  // D[3:0], S0, S1, Y, not_S0, not_S1

  // Sample when any input or select bit changes
  default clocking cb @(
      posedge S0 or negedge S0 or
      posedge S1 or negedge S1 or
      posedge D[0] or negedge D[0] or
      posedge D[1] or negedge D[1] or
      posedge D[2] or negedge D[2] or
      posedge D[3] or negedge D[3]
  ); endclocking

  // Functional correctness: when selects are known, Y equals the selected D bit
  assert property ( !$isunknown({S1,S0}) |-> (Y == D[{S1,S0}]) )
    else $error("mux4to1: Y must equal D[{S1,S0}] when selects are known");

  // Internal inverters must be exact complements
  assert property ( (not_S0 === ~S0) && (not_S1 === ~S1) )
    else $error("mux4to1: not_S0/1 must equal ~S0/~S1");

  // Decode must be one-hot when selects are known
  assert property ( !$isunknown({S1,S0}) |->
                    $onehot({(~S1 & ~S0), (~S1 & S0), (S1 & ~S0), (S1 & S0)}) )
    else $error("mux4to1: select decode not one-hot");

  // Y may only change if the selected D changes (with stable selects)
  assert property ( !$isunknown({S1,S0}) && $stable({S1,S0}) && $changed(Y)
                    |-> $changed(D[{S1,S0}]) )
    else $error("mux4to1: Y changed without selected D changing");

  // If selects are stable and selected D changes (known), Y must follow
  assert property ( !$isunknown({S1,S0}) && $stable({S1,S0}) &&
                    !$isunknown(D[{S1,S0}]) && $changed(D[{S1,S0}])
                    |-> $changed(Y) && (Y == D[{S1,S0}]) )
    else $error("mux4to1: Y did not follow selected D change");

  // Coverage: each select combination with both data values observed on Y
  cover property ( S1==0 && S0==0 && D[0]==0 && Y==0 );
  cover property ( S1==0 && S0==0 && D[0]==1 && Y==1 );
  cover property ( S1==0 && S0==1 && D[1]==0 && Y==0 );
  cover property ( S1==0 && S0==1 && D[1]==1 && Y==1 );
  cover property ( S1==1 && S0==0 && D[2]==0 && Y==0 );
  cover property ( S1==1 && S0==0 && D[2]==1 && Y==1 );
  cover property ( S1==1 && S0==1 && D[3]==0 && Y==0 );
  cover property ( S1==1 && S0==1 && D[3]==1 && Y==1 );

  // Coverage: data change on selected input propagates to Y with stable selects
  cover property ( !$isunknown({S1,S0}) && $stable({S1,S0}) &&
                   $changed(D[{S1,S0}]) && $changed(Y) && (Y==D[{S1,S0}]) );

endmodule

bind mux4to1 mux4to1_sva sva_mux4to1();