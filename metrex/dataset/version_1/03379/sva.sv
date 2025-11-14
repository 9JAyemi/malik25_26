// SVA for _4bit_binary_counter
// Concise checks for priority, counting, hold, wrap, and Qcc_n correctness.
// Bind this module to the DUT.

module _4bit_binary_counter_sva (
  input logic        CP,
  input logic        M,
  input logic [3:0]  D,
  input logic        LD_n,
  input logic        CLR_n,
  input logic [3:0]  Q,
  input logic        Qcc_n
);

  default clocking cb @(posedge CP); endclocking

  // Track past-valid to safely use $past()
  bit past_valid;
  always @(posedge CP) past_valid <= 1'b1;

  // Synchronous clear has highest priority and takes effect on the same clock
  assert property (cb !CLR_n |-> (Q == 4'h0));

  // Load has priority over count when not clearing
  assert property (cb disable iff (!CLR_n)
                     (!LD_n) |-> (Q == D));

  // Count when enabled (mod-16), masked to 4 bits
  assert property (cb disable iff (!past_valid || !CLR_n || !LD_n)
                     M |-> (Q == (($past(Q) + 4'd1) & 4'hF)));

  // Hold when not counting (no clear, no load)
  assert property (cb disable iff (!past_valid || !CLR_n || !LD_n)
                     !M |-> (Q == $past(Q)));

  // Q outputs should be known when not under clear
  assert property (cb disable iff (!CLR_n || !past_valid)
                     !$isunknown(Q));

  // Qcc_n must always reflect the complement of the current MSB of Q
  // (this will catch any 1-cycle lag)
  assert property (cb (!$isunknown({Qcc_n, Q[3]})) |-> (Qcc_n == ~Q[3]));

  // Optional: Qcc_n known when not under clear
  assert property (cb disable iff (!CLR_n || !past_valid)
                     !$isunknown(Qcc_n));

  // Coverage

  // See a clear
  cover property (cb !CLR_n && Q == 4'h0);

  // See a load
  cover property (cb CLR_n && !LD_n && Q == D);

  // See a count enable
  cover property (cb CLR_n && LD_n && M);

  // See wrap-around from 0xF to 0x0 while counting
  cover property (cb disable iff (!CLR_n || !LD_n)
                    past_valid && $past(M) && ($past(Q) == 4'hF) && (Q == 4'h0));

  // See MSB toggle and Qcc_n track it
  cover property (cb past_valid && $changed(Q[3]) && (Qcc_n == ~Q[3]));

endmodule

bind _4bit_binary_counter _4bit_binary_counter_sva sva_inst (
  .CP(CP),
  .M(M),
  .D(D),
  .LD_n(LD_n),
  .CLR_n(CLR_n),
  .Q(Q),
  .Qcc_n(Qcc_n)
);