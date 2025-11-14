// SVA for alt_ddrx_reset_sync and its instantiations in alt_ddrx_clock_and_reset
// Concise, high-quality checks and coverage

// Parameterized SVA bound to every alt_ddrx_reset_sync instance
module alt_ddrx_reset_sync_sva #(
  parameter int RESET_SYNC_STAGES = 4,
  parameter int NUM_RESET_OUTPUT  = 1
)(
  input  logic                         clk,
  input  logic                         reset_n,
  input  logic [NUM_RESET_OUTPUT-1:0]  reset_n_sync
);

  default clocking cb @(posedge clk); endclocking

  // Parameter sanity (required by implementation indexing)
  initial begin
    assert (RESET_SYNC_STAGES >= 2)
      else $error("alt_ddrx_reset_sync: RESET_SYNC_STAGES must be >= 2");
    assert (NUM_RESET_OUTPUT >= 1)
      else $error("alt_ddrx_reset_sync: NUM_RESET_OUTPUT must be >= 1");
  end

  // No unknowns on control signals
  assert property ( !$isunknown({reset_n, reset_n_sync}) );

  // While async reset is low, all outputs low
  assert property ( !reset_n |-> (reset_n_sync == '0) );

  // Asynchronous assertion is immediate
  always @(negedge reset_n)
    assert (reset_n_sync == '0)
      else $error("alt_ddrx_reset_sync: reset_n_sync not low on negedge reset_n");

  // All replicated outputs are always identical
  if (NUM_RESET_OUTPUT > 1) begin
    assert property ( reset_n_sync == {NUM_RESET_OUTPUT{reset_n_sync[0]}} );
  end

  // On reset release, outputs stay low for exactly RESET_SYNC_STAGES-1 clocks,
  // then go high on the RESET_SYNC_STAGES-th clock
  assert property ( $rose(reset_n) |-> (reset_n_sync == '0)[* (RESET_SYNC_STAGES-1)] );
  assert property ( disable iff (!reset_n) $rose(reset_n) |-> ##RESET_SYNC_STAGES (reset_n_sync == '1) );

  // Once high, outputs remain high until reset reasserts
  assert property ( disable iff (!reset_n) $past(reset_n_sync == '1) |-> (reset_n_sync == '1) );

  // Coverage: see both deassert and assert behaviors
  cover property ( $rose(reset_n) ##RESET_SYNC_STAGES (reset_n_sync == '1) );
  cover property ( $fell(reset_n) );

endmodule

// Bind the SVA to all instances of the reset synchronizer
bind alt_ddrx_reset_sync
  alt_ddrx_reset_sync_sva #(
    .RESET_SYNC_STAGES(RESET_SYNC_STAGES),
    .NUM_RESET_OUTPUT (NUM_RESET_OUTPUT )
  ) i_alt_ddrx_reset_sync_sva (
    .clk         (clk),
    .reset_n     (reset_n),
    .reset_n_sync(reset_n_sync)
  );