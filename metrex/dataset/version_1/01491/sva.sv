// SVA for d_ff_with_async_reset_set
module d_ff_with_async_reset_set_sva (
  input logic D,
  input logic CLK,
  input logic SCD,
  input logic SCE,
  input logic Q,
  input logic Q_N
);

  default clocking cb @(posedge CLK); endclocking

  // Inputs must be known at sampling
  assert property ( !$isunknown({D,SCD,SCE}) );

  // Outputs must become known after update
  assert property ( 1 |-> ##0 !$isunknown({Q,Q_N}) );

  // Complementary outputs (catch glitches as well)
  always @* assert (Q_N === ~Q);

  // Functional correctness with priority (sample post-NBA via ##0)
  assert property ( SCD |-> ##0 (Q==1'b0 && Q_N==1'b1) );
  assert property ( !SCD && SCE |-> ##0 (Q==1'b1 && Q_N==1'b0) );
  assert property ( !SCD && !SCE |-> ##0 (Q==D     && Q_N==~D) );

  // Explicit both-high precedence
  assert property ( SCD && SCE |-> ##0 (Q==1'b0 && Q_N==1'b1) );

  // Coverage: exercise all modes and both Q polarities
  cover property ( SCD );
  cover property ( !SCD && SCE );
  cover property ( !SCD && !SCE && (D==1'b0) );
  cover property ( !SCD && !SCE && (D==1'b1) );
  cover property ( SCD && SCE );       // precedence case
  cover property ( $rose(Q) );
  cover property ( $fell(Q) );

endmodule

bind d_ff_with_async_reset_set d_ff_with_async_reset_set_sva u_d_ff_with_async_reset_set_sva (.*);