// SVA for sky130_fd_sc_lp__iso0n (isolation 0, active-low sleep)
// Bind this checker to the DUT instance(s)

module sky130_fd_sc_lp__iso0n_sva (
  input logic X,
  input logic A,
  input logic SLEEP_B
);

  // Combinational equivalence holds at all times
  property p_eq;
    @(A or SLEEP_B or X) 1 |-> (X === (A & SLEEP_B));
  endproperty
  assert property (p_eq);

  // Clamp-low whenever sleeping, independent of A
  property p_clamp_sleep;
    @(A or SLEEP_B or X) (SLEEP_B === 1'b0) |-> ##0 (X === 1'b0);
  endproperty
  assert property (p_clamp_sleep);

  // Pass-through when awake and A is known
  property p_pass_awake;
    @(A or SLEEP_B or X) (SLEEP_B === 1'b1 && !$isunknown(A)) |-> ##0 (X === A);
  endproperty
  assert property (p_pass_awake);

  // Output known when inputs are known
  property p_known_out_when_known_in;
    @(A or SLEEP_B or X) (!$isunknown(A) && !$isunknown(SLEEP_B)) |-> ##0 (!$isunknown(X));
  endproperty
  assert property (p_known_out_when_known_in);

  // No output toggle on A changes while sleeping
  property p_no_toggle_in_sleep;
    @(A or SLEEP_B or X) (SLEEP_B === 1'b0 && $changed(A)) |-> ##0 (X === 1'b0 && !$changed(X));
  endproperty
  assert property (p_no_toggle_in_sleep);

  // Output tracks A when awake (and A changes to a known value)
  property p_track_when_awake;
    @(A or SLEEP_B or X) (SLEEP_B === 1'b1 && $changed(A) && !$isunknown(A)) |-> ##0 (X === A && $changed(X));
  endproperty
  assert property (p_track_when_awake);

  // Immediate response to sleep edges
  property p_sleep_fall_clamps;
    @(A or SLEEP_B or X) $fell(SLEEP_B) |-> ##0 (X === 1'b0);
  endproperty
  assert property (p_sleep_fall_clamps);

  property p_sleep_rise_passthru;
    @(A or SLEEP_B or X) $rose(SLEEP_B) |-> ##0 (X === A);
  endproperty
  assert property (p_sleep_rise_passthru);

  // Functional coverage: truth table and key transitions
  cover property (@(A or SLEEP_B or X) (A===1'b0 && SLEEP_B===1'b0) ##0 (X===1'b0));
  cover property (@(A or SLEEP_B or X) (A===1'b1 && SLEEP_B===1'b0) ##0 (X===1'b0));
  cover property (@(A or SLEEP_B or X) (A===1'b0 && SLEEP_B===1'b1) ##0 (X===1'b0));
  cover property (@(A or SLEEP_B or X) (A===1'b1 && SLEEP_B===1'b1) ##0 (X===1'b1));

  cover property (@(A or SLEEP_B or X) (SLEEP_B===1'b1 && A===1'b1) ##1 (SLEEP_B===1'b0 && X===1'b0)); // clamp from 1
  cover property (@(A or SLEEP_B or X) (SLEEP_B===1'b1 && A===1'b0) ##1 (SLEEP_B===1'b0 && X===1'b0)); // clamp from 0
  cover property (@(A or SLEEP_B or X) (SLEEP_B===1'b0 && X===1'b0) ##1 (SLEEP_B===1'b1 && X===A));   // wake passthrough
endmodule

bind sky130_fd_sc_lp__iso0n sky130_fd_sc_lp__iso0n_sva i_iso0n_sva (.X(X), .A(A), .SLEEP_B(SLEEP_B));