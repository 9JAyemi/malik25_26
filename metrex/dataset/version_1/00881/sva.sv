// SVA for reset_synchronizer
// Bind-friendly; connects to internals reset_synced and reset_synced_d
module reset_synchronizer_sva (
  input logic clk,
  input logic reset_n,
  input logic reset,

  // internal DUT regs (connected via bind)
  input logic        reset_synced,
  input logic [1:0]  reset_synced_d
);

  default clocking cb @(posedge clk); endclocking

  // Ensure $past(...,2) is valid before firing assertions
  logic [1:0] past_vld;
  always_ff @(posedge clk) past_vld <= {past_vld[0], 1'b1};
  default disable iff (!past_vld[1]);

  // Structural/functional correctness
  ap_map_out:      assert property (reset == reset_synced);
  ap_pipe_d:       assert property (reset_synced_d == {$past(reset_synced), $past(reset_n)});
  ap_func_next:    assert property (reset == ($past(reset_synced_d[1]) & ~($past(reset_synced_d[0]))));

  // Safety: output high only if input low 2 cycles earlier
  ap_hi_needs_lo2: assert property (reset |-> !$past(reset_n,2));

  // Deassertion guarantee: two consecutive high samples on reset_n force reset low
  ap_two_hi_zero:  assert property ($past(reset_n,1) && $past(reset_n,2) |-> reset == 1'b0);

  // X-propagation hygiene (only when history is known)
  ap_known_d:      assert property (!$isunknown({$past(reset_synced), $past(reset_n)}) |-> !$isunknown(reset_synced_d));
  ap_known_out:    assert property (!$isunknown($past(reset_synced_d)) |-> !$isunknown(reset));

  // Coverage: exercise all input-history combos and resulting output
  cp_assert:       cover property ($past(reset_synced_d) == 2'b10 && reset);
  cp_deassert00:   cover property ($past(reset_synced_d) == 2'b00 && !reset);
  cp_deassert01:   cover property ($past(reset_synced_d) == 2'b01 && !reset);
  cp_deassert11:   cover property ($past(reset_synced_d) == 2'b11 && !reset);
  cp_two_hi_zero:  cover property ($past(reset_n,2) && $past(reset_n,1) && !reset);

endmodule

// Example bind (place in a package or a separate sv file compiled with the DUT):
// bind reset_synchronizer reset_synchronizer_sva sva (.*,
//   .reset_synced(reset_synced),
//   .reset_synced_d(reset_synced_d)
// );