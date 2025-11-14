// SVA for reset_sync
// Bind into the DUT; focuses on functional correctness, latency, replication, and glitch avoidance

module reset_sync_sva #(
  parameter int RESET_SYNC_STAGES = 4,
  parameter int NUM_RESET_OUTPUT  = 1
)(
  input  logic                          clk,
  input  logic                          reset_n,
  input  logic [NUM_RESET_OUTPUT-1:0]   reset_n_sync,
  input  logic [RESET_SYNC_STAGES+NUM_RESET_OUTPUT-2:0] reset_reg
);
  localparam int W        = RESET_SYNC_STAGES + NUM_RESET_OUTPUT - 1;
  localparam int OUT_LSB  = RESET_SYNC_STAGES - 1;
  localparam int OUT_MSB  = W - 1;
  localparam int LAT      = RESET_SYNC_STAGES - 1;

  // Parameter sanity (matches RTL indexing of RESET_SYNC_STAGES-2)
  initial begin
    assert (RESET_SYNC_STAGES >= 2) else $error("RESET_SYNC_STAGES must be >= 2");
    assert (NUM_RESET_OUTPUT  >= 1) else $error("NUM_RESET_OUTPUT must be >= 1");
  end

  default clocking cb @(posedge clk); endclocking

  // Async assertion drives everything low immediately
  assert property (@(negedge reset_n) reset_reg == '0 && reset_n_sync == '0);

  // While reset is held low, everything stays low
  assert property (!reset_n |-> (reset_reg == '0 && reset_n_sync == '0));

  // Stage-0 forces 1 when reset_n is high
  assert property (reset_n |-> reset_reg[0] == 1'b1);

  // Pipeline shift correctness for the synchronizer chain
  genvar j;
  generate
    for (j = 1; j <= RESET_SYNC_STAGES-1; j++) begin : g_shift_chk
      assert property (disable iff (!reset_n) reset_reg[j] == $past(reset_reg[j-1]));
    end
    // Replication to output slice is from stage RESET_SYNC_STAGES-2
    for (j = OUT_LSB; j <= OUT_MSB; j++) begin : g_repl_chk
      assert property (disable iff (!reset_n) reset_reg[j] == $past(reset_reg[RESET_SYNC_STAGES-2]));
    end
  endgenerate

  // Outputs equal the replicated tap and are all identical
  assert property (disable iff (!reset_n)
                   reset_n_sync == {NUM_RESET_OUTPUT{$past(reset_reg[RESET_SYNC_STAGES-2])}});
  assert property (reset_n_sync == {NUM_RESET_OUTPUT{reset_n_sync[0]}});

  // Deassertion latency: outputs go high exactly LAT cycles after reset_n rises
  assert property ($rose(reset_n) |=> (reset_n_sync == '0)[*LAT] ##1 (reset_n_sync == '1));

  // Once high, outputs remain high while reset_n stays high (no spurious drop)
  assert property (disable iff (!reset_n) (reset_n_sync == '1) |-> $stable(reset_n_sync));

  // No X on outputs when reset_n is high
  assert property (reset_n |-> !$isunknown(reset_n_sync));

  // Coverage: see assert/deassert and the exact deassertion latency
  cover property ($fell(reset_n));
  cover property ($rose(reset_n));
  cover property ($rose(reset_n) ##LAT (reset_n_sync == '1));
  cover property ($rose(reset_n) ##LAT (reset_n_sync == '1) ##[1:$] $fell(reset_n) ##0 (reset_n_sync == '0));
endmodule

// Bind into the DUT
bind reset_sync reset_sync_sva #(
  .RESET_SYNC_STAGES(RESET_SYNC_STAGES),
  .NUM_RESET_OUTPUT (NUM_RESET_OUTPUT )
) i_reset_sync_sva (
  .clk          (clk),
  .reset_n      (reset_n),
  .reset_n_sync (reset_n_sync),
  .reset_reg    (reset_reg)
);