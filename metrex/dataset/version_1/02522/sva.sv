// SVA for AGC. Bind this to the DUT.
module AGC_sva #(parameter int target_level = 100,
                 parameter int step_size   = 1)
  (input logic clk);

  // Access DUT internals directly via bind scope: in, out, gain, sum

  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Parameter sanity (static)
  initial begin
    assert (step_size > 0)
      else $error("AGC step_size must be > 0");
    assert (target_level >= 0)
      else $error("AGC target_level must be >= 0");
  end

  // X/Z checks after first cycle
  a_no_x: assert property (past_valid |-> !$isunknown({in,out,gain,sum}));

  // Combinational output relation: out is LSB of in*gain = in & gain[0]
  a_out_lsb: assert property (out === (in & gain[0]));

  // sum is cleared every cycle
  a_sum_zero: assert property (past_valid |=> (sum == 16'd0));

  // Gain update rules based on previous sum
  a_gain_dec:  assert property (past_valid && (sum > target_level) |=> (gain == $past(gain) - step_size));
  a_gain_inc:  assert property (past_valid && (sum < target_level) |=> (gain == $past(gain) + step_size));
  a_gain_hold: assert property (past_valid && (sum == target_level) |=> (gain == $past(gain)));

  // Detect/forbid wraparound on gain updates
  a_no_underflow: assert property (past_valid && (sum > target_level) |-> ($past(gain) >= step_size))
                   else $error("AGC gain underflow on decrement");
  a_no_overflow:  assert property (past_valid && (sum < target_level) |-> ($past(gain) <= 8'hFF - step_size))
                   else $error("AGC gain overflow on increment");

  // Coverage: exercise all branches and edge cases
  c_dec:  cover property (past_valid && (sum > target_level) ##1 1);
  c_inc:  cover property (past_valid && (sum < target_level) ##1 1);
  c_hold: cover property (past_valid && (sum == target_level) ##1 1);

  c_gain_min: cover property (gain == 8'h00);
  c_gain_max: cover property (gain == 8'hFF);

  c_out1_when_in1: cover property (in && out);
  c_out0_when_in1: cover property (in && !out);

  // Corner coverage: observe potential wrap conditions
  c_underflow_cond: cover property (past_valid && (sum > target_level) && ($past(gain) < step_size));
  c_overflow_cond:  cover property (past_valid && (sum < target_level) && ($past(gain) > 8'hFF - step_size));

endmodule

bind AGC AGC_sva #(.target_level(target_level),
                   .step_size(step_size)) agc_sva_i (.clk(clk));