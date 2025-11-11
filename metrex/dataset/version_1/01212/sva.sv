// SVA for and4. Bind into the DUT; accesses internal nets directly.

module and4_sva;
  // Sample on any input edge
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge C or negedge C or
    posedge D or negedge D
  ); endclocking

  // Functional correctness (guarded against X/Z on inputs)
  assert property( !$isunknown({A,B})        |-> (and1_out == (A & B)) )
    else $error("and1_out != A&B");
  assert property( !$isunknown({C,D})        |-> (and2_out == (C & D)) )
    else $error("and2_out != C&D");
  assert property( !$isunknown({and1_out,and2_out}) |-> (Y == (and1_out & and2_out)) )
    else $error("Y != and1_out & and2_out");
  assert property( !$isunknown({A,B,C,D})    |-> (Y == (A & B & C & D)) )
    else $error("Y != A&B&C&D");

  // Known-ness: if inputs are known, all internal/outputs are known
  assert property( !$isunknown({A,B,C,D}) |-> !$isunknown({and1_out,and2_out,Y}) )
    else $error("Unknown on outputs with known inputs");

  // No spurious output changes without input activity
  assert property( @(posedge Y or negedge Y) $changed({A,B,C,D}) )
    else $error("Y changed without input change");

  // Internal outputs only change when their inputs change
  assert property( @(posedge and1_out or negedge and1_out) $changed({A,B}) )
    else $error("and1_out changed without A/B change");
  assert property( @(posedge and2_out or negedge and2_out) $changed({C,D}) )
    else $error("and2_out changed without C/D change");

  // Coverage: hit all 16 input combinations
  genvar i;
  for (i = 0; i < 16; i++) begin : gen_tt_cov
    localparam [3:0] V = i;
    cover property ( {A,B,C,D} == V );
  end

  // Coverage: observe all toggles on internal nets and output
  cover property( $rose(and1_out) );
  cover property( $fell(and1_out) );
  cover property( $rose(and2_out) );
  cover property( $fell(and2_out) );
  cover property( $rose(Y) );
  cover property( $fell(Y) );
endmodule

bind and4 and4_sva and4_sva_inst();