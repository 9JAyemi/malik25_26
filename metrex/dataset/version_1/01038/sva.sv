// SVA checker for aurora_201_STANDARD_CC_MODULE
// Concise but thorough checks of timing, causality, and gating

module aurora_201_STANDARD_CC_MODULE_sva
(
  input  logic                   USER_CLK,
  input  logic                   CHANNEL_UP,
  input  logic                   DCM_NOT_LOCKED, // unused in DUT; kept for interface completeness
  input  logic                   WARN_CC,
  input  logic                   DO_CC,

  // internal DUT signals
  input  logic [0:9]             prepare_count_r,
  input  logic [0:5]             cc_count_r,
  input  logic                   reset_r,

  input  logic [0:11]            count_13d_srl_r,
  input  logic                   count_13d_flop_r,
  input  logic                   inner_count_done_r,

  input  logic [0:14]            count_16d_srl_r,
  input  logic                   count_16d_flop_r,
  input  logic                   middle_count_done_c,

  input  logic [0:22]            count_24d_srl_r,
  input  logic                   count_24d_flop_r,
  input  logic                   cc_idle_count_done_c,

  input  logic                   start_cc_c
);

default clocking cb @(posedge USER_CLK); endclocking

// Basic reset/down behavior
property p_outputs_cleared_when_down;
  !CHANNEL_UP |=> (!DO_CC && !WARN_CC);
endproperty
assert property(p_outputs_cleared_when_down);

// Start CC on channel up rising
assert property ($rose(CHANNEL_UP) |-> start_cc_c);
assert property ($rose(CHANNEL_UP) |-> DO_CC);

// DO_CC pulse shape: exactly 6 cycles high per start, then low
property p_do_cc_pulse_len;
  disable iff (!CHANNEL_UP)
  start_cc_c |-> (DO_CC[*6] ##1 !DO_CC);
endproperty
assert property(p_do_cc_pulse_len);

// DO_CC causality
assert property ($rose(DO_CC) |-> start_cc_c);
assert property ($fell(DO_CC) |-> (!CHANNEL_UP || cc_count_r[5]));
assert property (DO_CC |-> !cc_count_r[5]); // cannot be held while deassert condition is true

// WARN_CC causality
assert property ($rose(WARN_CC) |-> cc_idle_count_done_c);
assert property ($fell(WARN_CC) |-> (!CHANNEL_UP || prepare_count_r[9]));

// prepare_count latency: 10 cycles from cc_idle_count_done_c
property p_prepare_latency;
  disable iff (!CHANNEL_UP)
  cc_idle_count_done_c |-> (!prepare_count_r[9][*9] ##1 prepare_count_r[9]);
endproperty
assert property(p_prepare_latency);

// start_cc from prepare_count[9]
assert property ($rose(prepare_count_r[9]) |-> (start_cc_c && DO_CC));

// Pulse hierarchy consistency
assert property (middle_count_done_c |-> inner_count_done_r);
assert property (cc_idle_count_done_c |-> middle_count_done_c);

// 13d feedback: while active, flop follows prior inner_done
property p_13d_flop_follows_inner;
  (CHANNEL_UP && !reset_r) |-> (count_13d_flop_r == $past(inner_count_done_r));
endproperty
assert property(p_13d_flop_follows_inner);

// 16d/24d flops only update on their enable pulses
assert property ((CHANNEL_UP && !reset_r && inner_count_done_r) |-> (count_16d_flop_r == $past(middle_count_done_c)));
assert property ((CHANNEL_UP && !reset_r && middle_count_done_c) |-> (count_24d_flop_r == $past(cc_idle_count_done_c)));

// SRLs are stable when not shifting (gated by their enables)
assert property ((CHANNEL_UP && !inner_count_done_r) |-> $stable(count_16d_srl_r));
assert property ((CHANNEL_UP && !middle_count_done_c) |-> $stable(count_24d_srl_r));

// Coverage: observe inner/middle/idle pulses and complete CC cycle
cover property (CHANNEL_UP && !reset_r ##1 $rose(inner_count_done_r));
cover property (CHANNEL_UP && !reset_r ##1 $rose(middle_count_done_c));
cover property (CHANNEL_UP && !reset_r ##1 $rose(cc_idle_count_done_c));
cover property ($rose(CHANNEL_UP) ##1 start_cc_c ##1 DO_CC[*6] ##1 !DO_CC);
cover property (cc_idle_count_done_c ##10 start_cc_c ##1 DO_CC[*6]);

endmodule

// Bind the checker into the DUT
bind aurora_201_STANDARD_CC_MODULE aurora_201_STANDARD_CC_MODULE_sva
(
  .USER_CLK               (USER_CLK),
  .CHANNEL_UP             (CHANNEL_UP),
  .DCM_NOT_LOCKED         (DCM_NOT_LOCKED),
  .WARN_CC                (WARN_CC),
  .DO_CC                  (DO_CC),

  .prepare_count_r        (prepare_count_r),
  .cc_count_r             (cc_count_r),
  .reset_r                (reset_r),

  .count_13d_srl_r        (count_13d_srl_r),
  .count_13d_flop_r       (count_13d_flop_r),
  .inner_count_done_r     (inner_count_done_r),

  .count_16d_srl_r        (count_16d_srl_r),
  .count_16d_flop_r       (count_16d_flop_r),
  .middle_count_done_c    (middle_count_done_c),

  .count_24d_srl_r        (count_24d_srl_r),
  .count_24d_flop_r       (count_24d_flop_r),
  .cc_idle_count_done_c   (cc_idle_count_done_c),

  .start_cc_c             (start_cc_c)
);