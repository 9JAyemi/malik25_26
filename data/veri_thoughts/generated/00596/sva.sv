module inverter_sva (
  input logic [0:0] ip,
  input logic [0:0] op,
  input logic clk,
  input logic ce,
  input logic clr
);

  ///// Output clear behavior /////
  // When clr is HIGH, op must be 0 in the same cycle.
  check_op_zero_when_clr_high: assert property (
    @(posedge clk) clr |-> (op == 1'b0)
  );

  // If clr is HIGH in two consecutive cycles, op stays 0.
  check_op_zero_stable_while_clr_high: assert property (
    @(posedge clk) ($past(clr) && clr) |-> (op == 1'b0)
  );

  ///// Update behavior with clock enable /////
  // If ce is HIGH and next cycle clr is LOW, op updates to bitwise NOT of ip from the ce cycle.
  check_update_inversion_on_ce_when_next_not_cleared: assert property (
    @(posedge clk) (ce ##1 !clr) |=> (op == ~ $past(ip,1))
  );

  // If ce is HIGH and next cycle clr is HIGH, clear overrides and op is 0.
  check_clear_overrides_update_after_ce: assert property (
    @(posedge clk) (ce ##1 clr) |=> (op == 1'b0)
  );

  // On a cycle after ce was HIGH, if clr is LOW, op equals bitwise NOT of previous ip.
  check_update_inversion_with_prior_ce_no_clr: assert property (
    @(posedge clk) ($past(ce) && !clr) |-> (op == ~ $past(ip))
  );

  ///// Hold behavior without clock enable /////
  // If ce was LOW and clr is LOW in both cycles, op holds its previous value.
  check_hold_when_no_ce_and_no_clr: assert property (
    @(posedge clk) ($past(!ce) && $past(!clr) && !clr) |-> (op == $past(op))
  );

  ///// Change qualification /////
  // If op changes while clr is LOW in consecutive cycles, the previous cycle must have had ce HIGH.
  check_op_change_requires_prior_ce_when_no_clr: assert property (
    @(posedge clk) (!clr && $past(!clr) && (op != $past(op))) |-> $past(ce)
  );

endmodule