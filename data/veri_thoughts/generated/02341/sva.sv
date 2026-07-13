module clock_gate_sva (
  input logic CLK,
  input logic EN,
  input logic TE,
  input logic ENCLK
);

  // ENCLK equals EN && TE after the clock edge update.
  check_enclk_equals_en_and_te_post: assert property (
    @(posedge CLK) ##0 (ENCLK == (EN && TE))
  );

  // If both EN and TE are high at the edge, ENCLK is set high that cycle.
  check_set_when_both_high: assert property (
    @(posedge CLK) (EN && TE) |-> ##0 (ENCLK == 1'b1)
  );

  // If either EN or TE is low at the edge, ENCLK is set low that cycle.
  check_clear_when_not_both_high: assert property (
    @(posedge CLK) !(EN && TE) |-> ##0 (ENCLK == 1'b0)
  );

  // ENCLK high implies both EN and TE were high at that edge.
  check_high_implies_inputs_high: assert property (
    @(posedge CLK) ##0 (ENCLK == 1'b1) |-> (EN && TE)
  );

  // ENCLK low implies not both EN and TE were high at that edge.
  check_low_implies_not_both_high: assert property (
    @(posedge CLK) ##0 (ENCLK == 1'b0) |-> !(EN && TE)
  );

  // If EN&&TE is unchanged across edges, ENCLK holds its value across edges.
  check_hold_when_inputs_unchanged: assert property (
    @(posedge CLK) ((EN && TE) == $past(EN && TE)) |-> ##0 (ENCLK == $past(ENCLK))
  );

  // TE low at the edge forces ENCLK low that cycle.
  check_te_low_forces_low: assert property (
    @(posedge CLK) (TE == 1'b0) |-> ##0 (ENCLK == 1'b0)
  );

  // EN low at the edge forces ENCLK low that cycle.
  check_en_low_forces_low: assert property (
    @(posedge CLK) (EN == 1'b0) |-> ##0 (ENCLK == 1'b0)
  );

endmodule