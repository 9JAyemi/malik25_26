// SVA for binary_counter
module binary_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic [15:0] q,
  input logic [3:0]  ov,
  input logic [3:1]  ena,
  input logic [3:0]  count
);
  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  a_no_x_ena: assert property (disable iff (reset) !$isunknown(ena));
  a_q_lower_zero: assert property (q[11:0] == 12'h000);
  a_ov_upper_zero: assert property (ov[3:1] == 3'b000);
  a_ov_is_bool: assert property (ov inside {4'h0,4'h1});

  // Reset behavior (synchronous)
  a_reset_vals_same_cycle: assert property (reset |-> (count==4'h0 && q==16'h0000 && ov==4'h0));

  // Register mapping uses previous count (due to nonblocking semantics)
  a_q_maps_prev_count:  assert property (disable iff (reset) q == {$past(count), 12'h000});
  a_ov_maps_prev_count: assert property (disable iff (reset) (ov[0] == ($past(count) == 4'hF)));

  // Functional next-state of count
  a_count_hold_when_e3_0: assert property (disable iff (reset)
                                           ($past(ena[3])==1'b0) |-> (count == $past(count)));

  a_count_next_fn: assert property (disable iff (reset)
    ($past(ena[3])==1'b1) |->
      ( count[3] == ~ $past(count[3]) ) &&
      ( count[2] == ( ($past(count[3]) && $past(ena[2])) ? ~ $past(count[2]) : $past(count[2]) ) ) &&
      ( count[1] == ( ($past(count[3]) && $past(ena[2]) && $past(count[2]) && $past(ena[1]))
                      ? ~ $past(count[1]) : $past(count[1]) ) ) &&
      ( count[0] == ( ($past(count[3]) && $past(ena[2]) && $past(count[2]) && $past(ena[1]) && $past(count[1]))
                      ? ~ $past(count[0]) : $past(count[0]) ) )
  );

  // Coverage: exercise each ripple depth and overflow
  c_toggle3:     cover property (disable iff (reset) $past(ena[3]) && !$past(count[3]));
  c_toggle32:    cover property (disable iff (reset) $past(ena[3]) && $past(count[3]) && $past(ena[2]) && !$past(count[2]));
  c_toggle321:   cover property (disable iff (reset) $past(ena[3]) && $past(count[3]) && $past(ena[2]) && $past(count[2]) && $past(ena[1]) && !$past(count[1]));
  c_toggle3210:  cover property (disable iff (reset) $past(ena[3]) && $past(count[3]) && $past(ena[2]) && $past(count[2]) && $past(ena[1]) && $past(count[1]) && !$past(count[0]));
  c_ov_assert:   cover property (disable iff (reset) ($past(count)==4'hF) && ov[0]);

endmodule

bind binary_counter binary_counter_sva u_binary_counter_sva (.*);


// SVA for overflow_counter (combinational)
module overflow_counter_sva (
  input logic [15:0] q,
  input logic [3:0]  ov
);
  // Immediate assertions for comb logic
  always_comb begin
    a_no_x_q_nib: assert (!$isunknown(q[15:12]));
    a_ov_popcnt:  assert (ov == (q[15] + q[14] + q[13] + q[12]));
    a_ov_range:   assert (ov inside {[4'd0:4'd4]});
    // Coverage for all popcount outcomes
    cover (ov==4'd0);
    cover (ov==4'd1);
    cover (ov==4'd2);
    cover (ov==4'd3);
    cover (ov==4'd4);
  end
endmodule

bind overflow_counter overflow_counter_sva u_overflow_counter_sva (.*);