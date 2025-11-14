// SVA for reset_synchronizer
module reset_synchronizer_sva #(
  parameter int NUM_RESET_OUTPUT   = 1,
  parameter int RESET_SYNC_STAGES  = 4
) (
  input  logic                       clk,
  input  logic                       reset_n,
  input  logic [NUM_RESET_OUTPUT-1:0] reset_n_sync
);

  default clocking cb @(posedge clk); endclocking

  // Parameter sanity (design requires >=2 due to indexing)
  initial begin
    assert (NUM_RESET_OUTPUT  >= 1) else $fatal(1,"NUM_RESET_OUTPUT must be >=1");
    assert (RESET_SYNC_STAGES >= 2) else $fatal(1,"RESET_SYNC_STAGES must be >=2");
  end

  // No X/Z on outputs
  ap_no_x: assert property (!$isunknown(reset_n_sync));

  // Outputs low whenever reset asserted
  ap_low_when_reset: assert property ((!reset_n) |-> (reset_n_sync == {NUM_RESET_OUTPUT{1'b0}}));

  // Async assertion is visible by next clk edge
  ap_async_seen: assert property ($fell(reset_n) |-> (reset_n_sync == {NUM_RESET_OUTPUT{1'b0}}));

  // Synchronous deassert: hold low for N-1 cycles, then all go high together on Nth cycle
  ap_release_latency: assert property (
    $rose(reset_n) |-> (reset_n_sync == {NUM_RESET_OUTPUT{1'b0}})[* (RESET_SYNC_STAGES-1)]
                     ##1 (reset_n_sync == {NUM_RESET_OUTPUT{1'b1}})
  );

  // Monotonic: no falling edges while reset_n is high
  ap_no_fall_while_high: assert property (disable iff (!reset_n) !$fell(reset_n_sync));

  // All outputs equal each cycle (flags any skew among outputs)
  ap_outputs_equal: assert property (reset_n_sync == {NUM_RESET_OUTPUT{reset_n_sync[0]}});

  // Coverage
  cp_deassert_sequence: cover property (
    $rose(reset_n)
      ##0 (reset_n_sync == {NUM_RESET_OUTPUT{1'b0}})[* (RESET_SYNC_STAGES-1)]
      ##1 (reset_n_sync == {NUM_RESET_OUTPUT{1'b1}})
  );

  cp_assert_sequence: cover property ($fell(reset_n) ##1 (reset_n_sync == {NUM_RESET_OUTPUT{1'b0}}));

endmodule

bind reset_synchronizer
  reset_synchronizer_sva #(
    .NUM_RESET_OUTPUT(NUM_RESET_OUTPUT),
    .RESET_SYNC_STAGES(RESET_SYNC_STAGES)
  ) reset_synchronizer_sva_i (
    .clk(clk),
    .reset_n(reset_n),
    .reset_n_sync(reset_n_sync)
  );