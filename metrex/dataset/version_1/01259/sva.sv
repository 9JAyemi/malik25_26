// SVA for wallace_multiplier
// Bind these assertions to the DUT; no DUT/Testbench changes required.

module wallace_multiplier_sva (
  input logic                 clk,
  input logic signed [7:0]    a,
  input logic signed [7:0]    b,
  input logic                 signed_ctrl,
  input logic signed [15:0]   result
);

  // Guard to skip first cycle
  logic seen;
  always_ff @(posedge clk) seen <= 1'b1;

  // 1-cycle latency functional correctness (signed/unsigned mode)
  property p_result_correct;
    @(posedge clk) disable iff (!seen)
      result
      == ( $past(signed_ctrl)
           ? $signed($past(a)) * $signed($past(b))
           : $unsigned($past(a)) * $unsigned($past(b)) );
  endproperty
  assert property (p_result_correct);

  // Result must be known when previous inputs are known
  property p_no_x_on_valid;
    @(posedge clk) disable iff (!seen)
      !$isunknown({$past(a), $past(b), $past(signed_ctrl)}) |-> !$isunknown(result);
  endproperty
  assert property (p_no_x_on_valid);

  // Result holds steady between clocks (no mid-cycle glitches)
  property p_result_stable_between_clks;
    @(posedge clk)
      1 |=> $stable(result) until_with (posedge clk);
  endproperty
  assert property (p_result_stable_between_clks);

  // If sampled inputs don’t change, sampled result doesn’t change
  property p_hold_if_inputs_hold;
    @(posedge clk) disable iff (!seen)
      $stable({$past(a), $past(b), $past(signed_ctrl)}) |-> $stable(result);
  endproperty
  assert property (p_hold_if_inputs_hold);

  // Algebraic sanity: zeroing behavior
  property p_zero_operand_yields_zero;
    @(posedge clk) disable iff (!seen)
      ($past(a) == 0 || $past(b) == 0) |-> (result == 0);
  endproperty
  assert property (p_zero_operand_yields_zero);

  // Algebraic sanity: sign of result in signed mode (allow zero as special case)
  property p_signed_sign_rule;
    @(posedge clk) disable iff (!seen)
      $past(signed_ctrl) && (result != 0)
      |-> (result[15] == ($past(a)[7] ^ $past(b)[7]));
  endproperty
  assert property (p_signed_sign_rule);

  // Coverage: exercise both modes and key corner cases (sampled one cycle earlier)
  cover property (@(posedge clk) disable iff (!seen)
                  $past(signed_ctrl) == 0 && $past(a) == 8'h00 && $past(b) == 8'h00);
  cover property (@(posedge clk) disable iff (!seen)
                  $past(signed_ctrl) == 0 && $past(a) == 8'hFF && $past(b) == 8'hFF);
  cover property (@(posedge clk) disable iff (!seen)
                  $past(signed_ctrl) == 1 && $past(a) == 8'sh80 && $past(b) == 8'sh80); // min*min
  cover property (@(posedge clk) disable iff (!seen)
                  $past(signed_ctrl) == 1 && $past(a) == -8'sd1 && $past(b) == 8'sd127); // -1 * max
  cover property (@(posedge clk) disable iff (!seen)
                  $rose(signed_ctrl) || $fell(signed_ctrl)); // mode toggling

endmodule

// Bind to DUT
bind wallace_multiplier wallace_multiplier_sva sva_i (.*);