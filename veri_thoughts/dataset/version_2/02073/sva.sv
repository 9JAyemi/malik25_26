module chatgpt_generate_JC_counter_sva (
  input  logic         clk,
  input  logic         rst_n,
  input  logic [63:0]  Q,
  input  logic [63:0]  lfsr
);

  // During reset, lfsr and Q must be zero.
  reset_drives_zero: assert property (
    @(posedge clk) (!rst_n) |-> (lfsr == 64'h0) && (Q == 64'h0)
  );

  // LFSR next-state equals {prev[62:0], prev[63]^prev[0]^prev[3]^prev[4]}.
  lfsr_next_equation: assert property (
    @(posedge clk) disable iff (!rst_n)
      $past(rst_n) |-> (lfsr == { $past(lfsr[62:0]),
                                  ($past(lfsr[63]) ^ $past(lfsr[0]) ^ $past(lfsr[3]) ^ $past(lfsr[4])) })
  );

  // LFSR upper bits shift: lfsr[63:1] == prev lfsr[62:0].
  lfsr_shift_consistency: assert property (
    @(posedge clk) disable iff (!rst_n)
      $past(rst_n) |-> (lfsr[63:1] == $past(lfsr[62:0]))
  );

  // LFSR feedback bit computation for bit 0.
  lfsr_feedback_bit: assert property (
    @(posedge clk) disable iff (!rst_n)
      $past(rst_n) |-> (lfsr[0] == ($past(lfsr[63]) ^ $past(lfsr[0]) ^ $past(lfsr[3]) ^ $past(lfsr[4])))
  );

  // Q lower nibble reflects previous-cycle lfsr taps {0,4,5,6} in that order.
  q_lower_from_prev_lfsr: assert property (
    @(posedge clk) disable iff (!rst_n)
      $past(rst_n) |-> (Q[3:0] == { $past(lfsr[0]), $past(lfsr[4]), $past(lfsr[5]), $past(lfsr[6]) })
  );

  // Q upper bits are always zero-extended.
  q_upper_zero_ext: assert property (
    @(posedge clk) disable iff (!rst_n)
      (Q[63:4] == 60'h0)
  );

  // Once lfsr is zero, it remains zero (absorbing state).
  lfsr_zero_absorbing: assert property (
    @(posedge clk) disable iff (!rst_n)
      $past(rst_n) && ($past(lfsr) == 64'h0) |-> (lfsr == 64'h0)
  );

  // If previous taps {0,4,5,6} were all zero, Q's lower nibble is zero.
  q_zero_from_zero_taps: assert property (
    @(posedge clk) disable iff (!rst_n)
      $past(rst_n) &&
      ({$past(lfsr[0]), $past(lfsr[4]), $past(lfsr[5]), $past(lfsr[6])} == 4'b0000)
      |-> (Q[3:0] == 4'b0000)
  );

  // LFSR MSB specifically shifts from previous bit 62.
  lfsr_msb_shifts: assert property (
    @(posedge clk) disable iff (!rst_n)
      $past(rst_n) |-> (lfsr[63] == $past(lfsr[62]))
  );

  // Q is stable if the contributing lfsr taps were unchanged over the prior cycle.
  q_stable_if_taps_unchanged: assert property (
    @(posedge clk) disable iff (!rst_n)
      $past(rst_n) && $past(rst_n,2) &&
      ({$past(lfsr[0]), $past(lfsr[4]), $past(lfsr[5]), $past(lfsr[6])} ==
       {$past(lfsr[0],2), $past(lfsr[4],2), $past(lfsr[5],2), $past(lfsr[6],2)})
      |-> (Q == $past(Q))
  );

endmodule