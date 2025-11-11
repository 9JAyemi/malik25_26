// SVA for nibble_match_count
// Binds into the DUT and checks shift/capture behavior and count updates.

module nibble_match_count_sva
(
  input  logic        clk,
  input  logic [7:0]  a,
  input  logic [7:0]  b,
  input  logic [2:0]  count,
  input  logic [3:0]  shift_reg_a,
  input  logic [3:0]  shift_reg_b
);

  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Shift registers must capture prior-cycle nibbles exactly (case equality tolerates X propagation)
  ap_sr_a_updates: assert property (shift_reg_a === $past(a[3:0]));
  ap_sr_b_updates: assert property (shift_reg_b === $past(b[3:0]));

  // Count increments by exactly one on a prior-cycle match of shift registers
  ap_cnt_inc_on_match: assert property (
    !$isunknown($past({shift_reg_a,shift_reg_b,count})) &&
    ($past(shift_reg_a) == $past(shift_reg_b))
    |-> count == $past(count) + 3'd1
  );

  // Count holds when prior-cycle shift registers do not match
  ap_cnt_hold_on_mismatch: assert property (
    !$isunknown($past({shift_reg_a,shift_reg_b,count})) &&
    ($past(shift_reg_a) != $past(shift_reg_b))
    |-> count == $past(count)
  );

  // Any change to count must be due to a prior-cycle match; step size limited to 0 or +1 (mod 8)
  ap_cnt_changes_implies_match: assert property (
    !$isunknown({count,$past(count),$past(shift_reg_a),$past(shift_reg_b)}) &&
    (count != $past(count))
    |-> $past(shift_reg_a) == $past(shift_reg_b)
  );

  ap_cnt_step_size: assert property (
    !$isunknown({count,$past(count)}) |-> (count == $past(count)) || (count == $past(count)+3'd1)
  );

  // Basic knownness after the first cycle for internal state
  ap_sr_known: assert property (!$isunknown(shift_reg_a) && !$isunknown(shift_reg_b));

  // Coverage: increment, hold, wrap, and back-to-back increments
  cover_match:   cover property (
    !$isunknown($past({shift_reg_a,shift_reg_b,count})) &&
    ($past(shift_reg_a) == $past(shift_reg_b)) ##1 (count == $past(count)+3'd1)
  );

  cover_nomatch: cover property (
    !$isunknown($past({shift_reg_a,shift_reg_b,count})) &&
    ($past(shift_reg_a) != $past(shift_reg_b)) ##1 (count == $past(count))
  );

  cover_wrap:    cover property (
    !$isunknown($past({shift_reg_a,shift_reg_b,count})) &&
    ($past(shift_reg_a) == $past(shift_reg_b)) && ($past(count) == 3'd7) ##1 (count == 3'd0)
  );

  cover_b2b_inc: cover property (
    (!$isunknown($past({shift_reg_a,shift_reg_b,count})) && ($past(shift_reg_a) == $past(shift_reg_b)))
    ##1 (!$isunknown($past({shift_reg_a,shift_reg_b,count})) && ($past(shift_reg_a) == $past(shift_reg_b)))
  );

endmodule

bind nibble_match_count nibble_match_count_sva sva_i (
  .clk(clk),
  .a(a),
  .b(b),
  .count(count),
  .shift_reg_a(shift_reg_a),
  .shift_reg_b(shift_reg_b)
);