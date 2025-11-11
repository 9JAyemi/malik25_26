// SVA for async_fifo_align_64in_out_rd_handshaking_flags

module async_fifo_align_64in_out_rd_handshaking_flags_sva (
  input logic        clk,
  input logic        Q,
  input logic        ram_valid_i,
  input logic        valid,
  // internal state taps
  input logic        Q_reg,
  input logic        ram_valid_d1_reg
);
  // establish safe use of $past
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // basic sanitization
  assert property (!$isunknown({Q, ram_valid_i, Q_reg, ram_valid_d1_reg, valid})));

  // flop tracking: each reg mirrors its input from previous cycle
  assert property (Q_reg == $past(Q));
  assert property (ram_valid_d1_reg == $past(ram_valid_i));

  // output function: AND of the two flops
  assert property (valid == (Q_reg && ram_valid_d1_reg));

  // equivalent past-based relation to input pins
  assert property (valid == ($past(Q) && $past(ram_valid_i)));

  // implication both ways (redundant with equivalence, but clearer debug)
  assert property ($past(Q && ram_valid_i) |-> valid);
  assert property (valid |-> $past(Q && ram_valid_i));

  // coverage: exercise all input combos and valid activity
  cover property (Q && ram_valid_i);
  cover property (Q && !ram_valid_i);
  cover property (!Q && ram_valid_i);
  cover property (!Q && !ram_valid_i);

  cover property ($rose(valid));
  cover property ($fell(valid));

  // typical handshake pulse: both high, then valid high next, then drop
  cover property ($past(Q && ram_valid_i) ##1 valid ##1 !valid);
endmodule

bind async_fifo_align_64in_out_rd_handshaking_flags
  async_fifo_align_64in_out_rd_handshaking_flags_sva
  u_async_fifo_align_64in_out_rd_handshaking_flags_sva (
    .clk                (clk),
    .Q                  (Q[0]),
    .ram_valid_i        (ram_valid_i),
    .valid              (valid),
    .Q_reg              (Q_reg[0]),
    .ram_valid_d1_reg   (ram_valid_d1_reg[0])
  );