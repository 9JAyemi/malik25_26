// SVA for DispScan
// Concise checks for state rotation, output mapping, gating by en, and basic coverage.
module DispScan_sva
(
  input  logic        clk,
  input  logic        en,
  input  logic [3:0]  in0,in1,in2,in3,
  input  logic        indip,
  input  logic [3:0]  select,out,
  input  logic        outdip,
  input  logic [1:0]  state
);
  localparam logic [1:0] S0=2'd0, S1=2'd1, S2=2'd2, S3=2'd3;

  default clocking cb @(posedge clk); endclocking

  // State rotation
  assert property ( $past(state)==S0 |-> state==S1 );
  assert property ( $past(state)==S1 |-> state==S2 );
  assert property ( $past(state)==S2 |-> state==S3 );
  assert property ( $past(state)==S3 |-> state==S0 );

  // select mapping and onehot behavior
  assert property ( en |-> select == (4'b0001 << state) );
  assert property ( !en |-> select == 4'b0000 );
  assert property ( $onehot0(select) );

  // out mapping when enabled
  assert property ( en && state==S0 |-> out==in0 );
  assert property ( en && state==S1 |-> out==in1 );
  assert property ( en && state==S2 |-> out==in2 );
  assert property ( en && state==S3 |-> out==in3 );

  // out holds while disabled (intentional latch behavior in RTL)
  assert property ( !en |-> $stable(out) throughout (!en) );

  // outdip behavior
  assert property ( !en |-> outdip==1'b0 );
  assert property ( en && state!=S1 |-> outdip==1'b0 );
  assert property ( en && state==S1 |-> outdip==indip );

  // Basic sanity: outputs not X/Z when enabled
  assert property ( en |-> !$isunknown({select,out,outdip}) );

  // Coverage
  cover property ( en && state==S0 ##1 en && state==S1 ##1 en && state==S2 ##1 en && state==S3 ##1 en && state==S0 );
  cover property ( en && state==S1 && indip==1'b1 );
  cover property ( en && state==S1 && indip==1'b0 );
  cover property ( !en ##1 en ); // disable then enable
endmodule

// Bind to DUT (including internal state)
bind DispScan DispScan_sva i_DispScan_sva(
  .clk(clk),
  .en(en),
  .in0(in0), .in1(in1), .in2(in2), .in3(in3),
  .indip(indip),
  .select(select),
  .out(out),
  .outdip(outdip),
  .state(state)
);