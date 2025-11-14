// SVA for lpddr2_cntrlr_p0_reset_sync
// Bindable checker focusing on functional latency, async behavior, and output consistency

module lpddr2_cntrlr_p0_reset_sync_sva
  #(parameter int RESET_SYNC_STAGES = 4,
    parameter int NUM_RESET_OUTPUT  = 1)
(
  input  logic                        clk,
  input  logic                        reset_n,
  input  logic [NUM_RESET_OUTPUT-1:0] reset_n_sync
);
  localparam int M = NUM_RESET_OUTPUT;
  localparam int N = RESET_SYNC_STAGES;
  wire [M-1:0] ALL0 = {M{1'b0}};
  wire [M-1:0] ALL1 = {M{1'b1}};

  default clocking cb @(posedge clk); endclocking

  // Outputs never X/Z once reset is deasserted
  assert property (disable iff (!reset_n) !$isunknown(reset_n_sync));

  // All outputs are identical at all times
  assert property (reset_n_sync == {M{reset_n_sync[0]}});

  // While in reset at clock edges, outputs are 0
  assert property ((!reset_n) |-> (reset_n_sync == ALL0));

  // On async assertion of reset, outputs drop to 0 immediately
  assert property (@(negedge reset_n) 1 |-> (reset_n_sync == ALL0));

  // Deassertion latency: remain 0 for N-1 cycles, then 1s on the Nth cycle
  assert property ($rose(reset_n)
                   |=> (reset_n_sync == ALL0)[* (N-1)] ##1 (reset_n_sync == ALL1));

  // Once high after latency, stay high until reset asserts again
  assert property ($rose(reset_n)
                   |=> ##N ((reset_n_sync == ALL1) throughout reset_n));

  // No falling edge on outputs while reset_n is high
  assert property (disable iff (!reset_n) !$fell(reset_n_sync[0]));

  // Coverage
  cover property ($rose(reset_n));
  cover property ($rose(reset_n)
                  |=> (reset_n_sync == ALL0)[* (N-1)] ##1 (reset_n_sync == ALL1));
  cover property (@(negedge reset_n) (reset_n_sync == ALL0));
  cover property ($rose(reset_n) |=> ##N (reset_n_sync == ALL1)[*3]);

endmodule

bind lpddr2_cntrlr_p0_reset_sync
  lpddr2_cntrlr_p0_reset_sync_sva
    #(.RESET_SYNC_STAGES(RESET_SYNC_STAGES),
      .NUM_RESET_OUTPUT(NUM_RESET_OUTPUT))
  i_lpddr2_cntrlr_p0_reset_sync_sva
    (.clk(clk), .reset_n(reset_n), .reset_n_sync(reset_n_sync));