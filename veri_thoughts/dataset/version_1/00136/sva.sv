// SVA for tracking_camera_system_altpll_0_dffpipe_l2c
// Bindable, concise, and focused on pipeline correctness and coverage

module tracking_camera_system_altpll_0_dffpipe_l2c_sva
(
  input  logic clock,
  input  logic d,
  input  logic q,
  input  logic prn,
  input  logic sclr,
  input  logic dffe4a,
  input  logic dffe5a,
  input  logic dffe6a
);

  // Control pins as coded (constant)
  assert property (@(posedge clock) prn && !sclr);

  // Stage-to-stage transfer (safe at time 0 via $past default arg)
  assert property (@(posedge clock) dffe4a == $past(d,       1, dffe4a));
  assert property (@(posedge clock) dffe5a == $past(dffe4a,  1, dffe5a));
  assert property (@(posedge clock) dffe6a == $past(dffe5a,  1, dffe6a));

  // End-to-end latency: q is d delayed by 3 cycles (safe start)
  assert property (@(posedge clock) q == $past(d, 3, q));

  // Priority preset when prn goes low (active-low)
  assert property (@(posedge clock) !prn |=> (dffe4a && dffe5a && dffe6a));

  // Hold behavior when prn=1 and sclr=1 (no load path)
  assert property (@(posedge clock) (prn && sclr) |=> (dffe4a == $past(dffe4a) &&
                                                       dffe5a == $past(dffe5a) &&
                                                       dffe6a == $past(dffe6a)));

  // X/Z sanitation once pipeline has history
  assert property (@(posedge clock) 1 |-> ##3 !$isunknown({d,q,dffe4a,dffe5a,dffe6a}));

  // Coverage: observe both polarities propagating through the 3-stage pipe
  cover  property (@(posedge clock) $rose(d) |-> ##3 $rose(q));
  cover  property (@(posedge clock) $fell(d) |-> ##3 $fell(q));

  // Coverage: preset and hold branches (useful for formal)
  cover  property (@(posedge clock) !prn);
  cover  property (@(posedge clock) prn && sclr);

endmodule

bind tracking_camera_system_altpll_0_dffpipe_l2c
  tracking_camera_system_altpll_0_dffpipe_l2c_sva
  sva_i (
    .clock (clock),
    .d     (d[0]),
    .q     (q[0]),
    .prn   (prn),
    .sclr  (sclr),
    .dffe4a(dffe4a[0]),
    .dffe5a(dffe5a[0]),
    .dffe6a(dffe6a[0])
  );