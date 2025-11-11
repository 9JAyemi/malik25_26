// SVA for time_compare
module time_compare_sva
  (input  [63:0] time_now,
   input  [63:0] trigger_time,
   input         now,
   input         early,
   input         late,
   input         too_early);

  // Known-input guard
  wire inputs_known = !$isunknown({time_now, trigger_time});

  // Outputs must be known when inputs are known
  assert property (@(*) disable iff (!inputs_known)
                   !$isunknown({now, early, late, too_early}));

  // Functional correctness
  assert property (@(*) disable iff (!inputs_known)
                   now == (time_now == trigger_time));
  assert property (@(*) disable iff (!inputs_known)
                   late == (time_now > trigger_time));
  assert property (@(*) disable iff (!inputs_known)
                   early == (time_now < trigger_time));

  // Mutual exclusivity / completeness
  assert property (@(*) disable iff (!inputs_known)
                   $onehot({now, early, late}));

  // Structural relation for early and constant too_early
  assert property (@(*) disable iff (!inputs_known)
                   early == (~now & ~late));
  assert property (@(*) too_early === 1'b0);

  // Coverage: all outcomes + key edges
  cover property (@(*) inputs_known && (time_now == trigger_time));            // now
  cover property (@(*) inputs_known && (time_now >  trigger_time));            // late
  cover property (@(*) inputs_known && (time_now <  trigger_time));            // early
  cover property (@(*) inputs_known && (time_now == trigger_time + 64'd1));    // just late
  cover property (@(*) inputs_known && (trigger_time == time_now + 64'd1));    // just early
  cover property (@(*) inputs_known && (time_now == 64'h0 &&
                                        trigger_time == 64'hFFFF_FFFF_FFFF_FFFF));
  cover property (@(*) inputs_known && (time_now == 64'hFFFF_FFFF_FFFF_FFFF &&
                                        trigger_time == 64'h0));

endmodule

bind time_compare time_compare_sva sva_i (.*);