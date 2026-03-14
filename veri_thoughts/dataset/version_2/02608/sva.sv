module xor_shift_registers_fixed_sva (
  input logic clk,
  input logic reset,
  input logic d,
  input logic q,
  input logic [3:0] sr1,
  input logic [1:0] sr2
);
  // Clock: clk (posedge). Reset: reset (active-high, synchronous).
  // Logic: sequential sr1/sr2 updates; combinational q = sr1[0] ^ sr2[1].

  // Synchronous reset clears both shift registers to zero.
  reset_clears_registers: assert property (
    @(posedge clk) reset |-> (sr1 == 4'b0000) && (sr2 == 2'b00)
  );

  // During reset, q is LOW (XOR of cleared bits).
  reset_q_low: assert property (
    @(posedge clk) reset |-> (q == 1'b0)
  );

  // When not reset, sr1 rotates left by one bit.
  check_sr1_rotates_left: assert property (
    @(posedge clk) disable iff (reset) sr1 == { $past(sr1)[2:0], $past(sr1)[3] }
  );

  // sr1[0] takes previous sr1[3] when not reset.
  check_sr1_bit0_from_prev_bit3: assert property (
    @(posedge clk) disable iff (reset) sr1[0] == $past(sr1[3])
  );

  // sr1[1] takes previous sr1[0] when not reset.
  check_sr1_bit1_from_prev_bit0: assert property (
    @(posedge clk) disable iff (reset) sr1[1] == $past(sr1[0])
  );

  // sr2[0] loads current d when not reset.
  check_sr2_bit0_loads_d: assert property (
    @(posedge clk) disable iff (reset) sr2[0] == d
  );

  // sr2[1] takes previous sr2[0] when not reset.
  check_sr2_bit1_from_prev_bit0: assert property (
    @(posedge clk) disable iff (reset) sr2[1] == $past(sr2[0])
  );

  // If previous cycle was not reset, sr2[1] equals previous d.
  check_sr2_bit1_is_prev_d: assert property (
    @(posedge clk) disable iff (reset) (!$past(reset)) |-> (sr2[1] == $past(d))
  );

  // q matches XOR of sr1[0] and sr2[1] when not reset.
  check_q_equals_xor: assert property (
    @(posedge clk) disable iff (reset) q == (sr1[0] ^ sr2[1])
  );

  // Once zero (outside reset), sr1 stays zero due to rotation.
  check_sr1_zero_sticky: assert property (
    @(posedge clk) disable iff (reset) (sr1 == 4'b0000) |=> (sr1 == 4'b0000)
  );

endmodule