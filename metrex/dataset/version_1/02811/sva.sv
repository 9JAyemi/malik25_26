// SVA for xor_shift_registers_fixed
// Bindable checker that verifies reset behavior, state updates, and output function.

module xor_shift_registers_fixed_sva (
  input logic        clk,
  input logic        reset,
  input logic        d,
  input logic        q,
  input logic [3:0]  sr1,
  input logic [1:0]  sr2
);
  default clocking cb @(posedge clk); endclocking

  // Reset effects (synchronous): one cycle after reset high, state must be cleared
  assert property ($past(reset) |-> (sr1 == 4'b0 && sr2 == 2'b00));

  // State update when not in reset
  assert property (disable iff (reset) sr1 == { $past(sr1[2:0]), $past(sr1[3]) });
  assert property (disable iff (reset) sr2 == { $past(sr2[0]), d });

  // Output function
  assert property (q == (sr1[0] ^ sr2[1]));

  // Basic X-safety after a reset has occurred
  assert property ($past(reset) |-> !(^sr1 === 1'bX) && !(^sr2 === 1'bX) && !(q === 1'bX));

  // Coverage
  cover property (reset);                       // reset seen
  cover property (disable iff (reset) $rose(q));
  cover property (disable iff (reset) $fell(q));
  cover property (disable iff (reset) sr2 == 2'b01); // sr2 demonstrates shifting
endmodule

// Bind into the DUT
bind xor_shift_registers_fixed xor_shift_registers_fixed_sva u_xor_shift_registers_fixed_sva (
  .clk  (clk),
  .reset(reset),
  .d    (d),
  .q    (q),
  .sr1  (sr1),
  .sr2  (sr2)
);