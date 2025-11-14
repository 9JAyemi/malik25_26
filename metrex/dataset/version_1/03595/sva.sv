// SVA for dffr_9
module dffr_9_sva #(parameter WIDTH=9)
(
  input  logic               clk,
  input  logic               reset,
  input  logic [WIDTH-1:0]   d,
  input  logic [WIDTH-1:0]   q
);

  default clocking cb @(posedge clk); endclocking

  // Async reset: clear immediately on reset rise
  property p_async_clear_on_rise;
    @(posedge reset) ##0 (q == '0);
  endproperty
  assert property (p_async_clear_on_rise);

  // While in reset, q must be zero at every clock sample
  property p_q_zero_while_reset;
    reset |-> (q == '0);
  endproperty
  assert property (p_q_zero_while_reset);

  // Functional behavior: 1-cycle latency DFF when not in reset
  property p_q_tracks_d;
    disable iff (reset) (q == $past(d));
  endproperty
  assert property (p_q_tracks_d);

  // No spurious q change: if d was unchanged over last two cycles, q must hold
  property p_no_spurious_q_change;
    disable iff (reset) ($past(d) == $past(d,2)) |-> (q == $past(q));
  endproperty
  assert property (p_no_spurious_q_change);

  // X/Z hygiene
  property p_q_not_x_in_reset;
    reset |-> (!$isunknown(q) && q == '0);
  endproperty
  assert property (p_q_not_x_in_reset);

  property p_no_x_when_used;
    !reset |-> (!$isunknown(d) && !$isunknown(q));
  endproperty
  assert property (p_no_x_when_used);

  // Coverage
  cover property (@(posedge clk) reset ##1 !reset);           // saw a reset pulse and release
  cover property (@(posedge clk) !reset ##1 (q == $past(d))); // at least one D->Q transfer
  cover property (@(posedge clk) !reset && ($past(d) != '0) ##1 (q != '0)); // non-zero propagated
  cover property (@(posedge clk) !reset && ($past(d) == '1) ##1 (q == '1)); // all-ones propagated

endmodule

bind dffr_9 dffr_9_sva #(.WIDTH(9)) u_dffr_9_sva (.*);