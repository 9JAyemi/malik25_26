// SVA for Reset_Synchronizer
// Focus: concise, high-quality checks and coverage

module Reset_Synchronizer_sva (
  input clk,
  input rst,
  input rst_sync,
  input rst_sync_ff1,
  input rst_sync_ff2
);

  // track valid past cycles (skip initial cycles)
  logic past1, past2;
  initial begin past1 = 1'b0; past2 = 1'b0; end
  always @(posedge clk) begin
    past1 <= 1'b1;
    past2 <= past1;
  end

  default clocking cb @(posedge clk); endclocking

  // Pipeline correctness
  assert property (past1 |-> rst_sync_ff1 == $past(rst));
  assert property (past1 |-> rst_sync_ff2 == $past(rst_sync_ff1));
  assert property (rst_sync == ~rst_sync_ff2);

  // One-cycle inverted mapping from rst to rst_sync
  assert property (past1 |-> rst_sync == ~ $past(rst));
  assert property (past1 && $rose(rst) |=> $fell(rst_sync));
  assert property (past1 && $fell(rst) |=> $rose(rst_sync));

  // Output only changes due to prior rst change
  assert property (past1 && $changed(rst_sync) |-> $changed($past(rst)));

  // No X after two clocks
  assert property (past2 |-> !$isunknown({rst_sync_ff1, rst_sync_ff2, rst_sync}));

  // Coverage: both edges propagate
  cover property ($rose(rst) ##1 $fell(rst_sync));
  cover property ($fell(rst) ##1 $rose(rst_sync));

endmodule

bind Reset_Synchronizer Reset_Synchronizer_sva
  i_reset_sync_sva(.clk(clk),
                   .rst(rst),
                   .rst_sync(rst_sync),
                   .rst_sync_ff1(rst_sync_ff1),
                   .rst_sync_ff2(rst_sync_ff2));