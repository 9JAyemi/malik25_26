module clock_phase_shifter_sva (
  input logic clk,
  input logic [3:0] phase_shift_amount,
  input logic clk_phase_shifted,
  input logic [3:0] counter
);

  // On a match, next cycle counter resets to 0 and output toggles.
  check_match_resets_and_toggles: assert property (
    @(posedge clk) (counter == phase_shift_amount) |=> (counter == 4'd0) && (clk_phase_shifted != $past(clk_phase_shifted))
  );

  // On no match, next cycle counter increments by 1 and output holds.
  check_no_match_increments_and_holds: assert property (
    @(posedge clk) (counter != phase_shift_amount) |=> (counter == $past(counter) + 4'd1) && (clk_phase_shifted == $past(clk_phase_shifted))
  );

  // A toggle of clk_phase_shifted occurs only when the previous cycle matched.
  check_toggle_only_on_match: assert property (
    @(posedge clk) (clk_phase_shifted != $past(clk_phase_shifted)) |-> ($past(counter) == $past(phase_shift_amount))
  );

  // Whenever clk_phase_shifted toggles, the counter is 0 in the same cycle.
  check_toggle_implies_counter_zero: assert property (
    @(posedge clk) (clk_phase_shifted != $past(clk_phase_shifted)) |-> (counter == 4'd0)
  );

  // If counter becomes 0, then last cycle was either a match or an overflow from 4'hF.
  check_zero_next_implies_match_or_overflow: assert property (
    @(posedge clk) (counter == 4'd0) |-> (($past(counter) == 4'hF) || ($past(counter) == $past(phase_shift_amount)))
  );

  // If last counter was 4'hF and no match, then we wrapped to 0 and output held.
  check_overflow_wrap_and_hold: assert property (
    @(posedge clk) ($past(counter) == 4'hF && $past(counter) != $past(phase_shift_amount)) |-> (counter == 4'd0) && (clk_phase_shifted == $past(clk_phase_shifted))
  );

  // On a match (and not at 4'hF), next counter is not equal to prev+1 (it resets instead).
  check_match_blocks_increment_when_not_max: assert property (
    @(posedge clk) (counter == phase_shift_amount && $past(counter) != 4'hF) |=> (counter != ($past(counter) + 4'd1))
  );

  // Counter update each cycle is either increment-by-one or reset-to-zero.
  check_counter_update_form: assert property (
    @(posedge clk) 1'b1 |=> (counter == ($past(counter) + 4'd1)) || (counter == 4'd0)
  );

endmodule