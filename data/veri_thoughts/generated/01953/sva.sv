module shift_register_sva (
  input logic clk,
  input logic load,
  input logic [3:0] p,
  input logic [3:0] q,
  input logic [3:0] q_bar
);

  // q_bar is always the bitwise inverse of q in the next cycle.
  check_qbar_inverts_q_next: assert property (
    @(posedge clk) 1'b1 |=> (q_bar == ~q)
  );

  // When load is HIGH, next q equals current p.
  check_load_sets_q: assert property (
    @(posedge clk) ($past(1'b1) && load) |=> (q == $past(p))
  );

  // When load is HIGH, next q_bar equals bitwise NOT of current p.
  check_load_sets_qbar: assert property (
    @(posedge clk) ($past(1'b1) && load) |=> (q_bar == ~$past(p))
  );

  // When load is LOW, next q shifts left with zero inserted at LSB.
  check_shift_sets_q: assert property (
    @(posedge clk) ($past(1'b1) && !load) |=> (q == {$past(q)[2:0], 1'b0})
  );

  // When load is LOW, next q_bar equals bitwise NOT of the shifted value.
  check_shift_sets_qbar: assert property (
    @(posedge clk) ($past(1'b1) && !load) |=> (q_bar == ~{$past(q)[2:0], 1'b0})
  );

  // When load is LOW, next q[0] is 0 (zero inserted at LSB).
  check_shift_lsb_zero: assert property (
    @(posedge clk) ($past(1'b1) && !load) |=> (q[0] == 1'b0)
  );

  // When load is LOW, next q[3] equals previous q[2] (left shift).
  check_shift_msb_from_q2: assert property (
    @(posedge clk) ($past(1'b1) && !load) |=> (q[3] == $past(q[2]))
  );

  // When load is LOW, next q[2:1] equals previous q[1:0] (left shift).
  check_shift_middle_bits_from_q10: assert property (
    @(posedge clk) ($past(1'b1) && !load) |=> (q[2:1] == $past(q[1:0]))
  );

endmodule