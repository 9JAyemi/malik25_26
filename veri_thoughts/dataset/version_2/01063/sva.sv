module flip_flops_sva (
  input logic D,
  input logic J,
  input logic K,
  input logic T,
  input logic S,
  input logic R,
  input logic CLK,
  input logic Q_D,
  input logic Q_JK,
  input logic Q_T,
  input logic Q_SR
);
  // DFF: Q_D captures D on rising edge (checked at next rising edge).
  check_dff_capture: assert property (
    @(posedge CLK) 1'b1 |=> (Q_D === $past(D))
  );

  // JKFF: J=0,K=0 -> hold previous value (checked at next falling edge).
  check_jkff_hold_00: assert property (
    @(negedge CLK) ({J,K} == 2'b00) |=> (Q_JK === $past(Q_JK))
  );
  // JKFF: J=0,K=1 -> reset to 0 (checked at next falling edge).
  check_jkff_reset_01: assert property (
    @(negedge CLK) ({J,K} == 2'b01) |=> (Q_JK == 1'b0)
  );
  // JKFF: J=1,K=0 -> set to 1 (checked at next falling edge).
  check_jkff_set_10: assert property (
    @(negedge CLK) ({J,K} == 2'b10) |=> (Q_JK == 1'b1)
  );
  // JKFF: J=1,K=1 -> toggle (checked at next falling edge).
  check_jkff_toggle_11: assert property (
    @(negedge CLK) ({J,K} == 2'b11) |=> (Q_JK === ~$past(Q_JK))
  );

  // TFF: when T=1, toggle on rising edge (checked at next rising edge).
  check_tff_toggle_when_T1: assert property (
    @(posedge CLK) (T == 1'b1) |=> (Q_T === ~$past(Q_T))
  );
  // TFF: when T=0, hold on rising edge (checked at next rising edge).
  check_tff_hold_when_T0: assert property (
    @(posedge CLK) (T == 1'b0) |=> (Q_T === $past(Q_T))
  );

  // SRFF: S=0,R=0 -> hold previous value (checked at next falling edge).
  check_srff_hold_00: assert property (
    @(negedge CLK) ({S,R} == 2'b00) |=> (Q_SR === $past(Q_SR))
  );
  // SRFF: S=0,R=1 -> reset to 0 (checked at next falling edge).
  check_srff_reset_01: assert property (
    @(negedge CLK) ({S,R} == 2'b01) |=> (Q_SR == 1'b0)
  );
  // SRFF: S=1,R=0 -> set to 1 (checked at next falling edge).
  check_srff_set_10: assert property (
    @(negedge CLK) ({S,R} == 2'b10) |=> (Q_SR == 1'b1)
  );
endmodule