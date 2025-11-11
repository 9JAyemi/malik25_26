// SVA checkers and binds for the provided design

// ------------------ t_ff assertions ------------------
module tff_sva (input logic clk, input logic t, input logic q);
  default clocking cb @(posedge clk); endclocking

  // q must be a one-cycle pulse iff t changed since last clk
  a_tff_toggle_exact: assert property (disable iff ($initstate)
                                       ($changed(t) <-> q));

  // Coverage: capture both edges of t producing a pulse on q
  c_tff_rose_pulse:  cover property ($rose(t) ##0 q);
  c_tff_fall_pulse:  cover property ($fell(t) ##0 q);
endmodule

bind t_ff tff_sva tff_chk(.clk(clk), .t(t), .q(q));


// ------------------ bcd_counter assertions ------------------
module bcd_counter_sva (input logic clk,
                        input logic reset,
                        input logic [2:0] ena,
                        input logic [3:0] count);
  default clocking cb @(posedge clk); endclocking

  // Synchronous reset to 0 and remain 0 while reset is asserted
  a_bcd_reset_now:    assert property (reset |-> (count == 4'd0));
  a_bcd_reset_hold:   assert property (reset |=> (count == 4'd0));

  // BCD range invariant (0..9)
  a_bcd_in_range:     assert property (!reset |-> (count inside {[4'd0:4'd9]}));

  // Hold when disabled (ena[0]==0), regardless of ena[2:1]
  a_hold_when_dis:    assert property (!$past(reset) && !$past(ena[0])
                                       |-> count == $past(count));

  // Increment behavior when enabled: 0..8 -> +1
  a_inc_when_en:      assert property (!$past(reset) && $past(ena[0]) &&
                                       ($past(count) inside {[4'd0:4'd8]})
                                       |-> count == $past(count) + 4'd1);

  // Rollover 9 -> 0 when enabled
  a_roll_when_en:     assert property (!$past(reset) && $past(ena[0]) &&
                                       ($past(count) == 4'd9)
                                       |-> count == 4'd0);

  // Coverage: hit 9->0 rollover and a disabled hold
  c_bcd_roll:         cover property (!$past(reset) && $past(ena[0]) &&
                                       ($past(count)==4'd9) && (count==4'd0));
  c_bcd_hold:         cover property (!$past(reset) && !$past(ena[0]) &&
                                       (count == $past(count)));
endmodule

bind bcd_counter bcd_counter_sva bcd_chk(.clk(clk), .reset(reset), .ena(ena), .count(count));


// ------------------ top-level end-to-end assertions ------------------
module top_sva (input logic clk,
                input logic reset,
                input logic t,
                input logic [2:0] ena,
                input logic t_ff_q,
                input logic [3:0] bcd_count,
                input logic [15:0] q);
  default clocking cb @(posedge clk); endclocking

  // Exact functional mapping into q
  a_func_exact: assert property (
      q == ( {bcd_count,1'b0} | (t_ff_q ? 16'h0001 : 16'h0000) )
  );

  // Bitwise sanity (redundant but debuggable)
  a_q0_from_tff:  assert property (q[0] == t_ff_q);
  a_q_low_nibble: assert property (q[4:1] == bcd_count);
  a_q_hi_zero:    assert property (q[15:5] == 11'h000);

  // End-to-end: a toggle of t creates a q[0] pulse next cycle
  a_t_to_q0_pulse: assert property (disable iff ($initstate || reset)
                                    $changed(t) |=> (q[0] == 1'b1));

  // If t stable, no q[0] pulse next cycle
  a_t_stable_no_pulse: assert property (disable iff ($initstate || reset)
                                        !$changed(t) |=> (q[0] == 1'b0));

  // No X/Z on key observable signals after init/reset
  a_no_unknowns: assert property (disable iff ($initstate || reset)
                                  !$isunknown({t_ff_q, bcd_count, q}));
  
  // Coverage: observe an end-to-end pulse through the path
  c_end2end_pulse: cover property (disable iff (reset)
                                   $rose(t) |=> q[0]);
endmodule

bind top_module top_sva topchk(.clk(clk),
                               .reset(reset),
                               .t(t),
                               .ena(ena),
                               .t_ff_q(t_ff_q),
                               .bcd_count(bcd_count),
                               .q(q));