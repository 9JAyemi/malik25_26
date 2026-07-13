module DFF_AR_sva (
  input logic CLK,
  input logic RST,   // Active-LOW asynchronous reset
  input logic D,
  input logic Q,
  input logic QN
);

  ///// Reset behavior /////
  // While reset is asserted low, outputs are forced to 0/1.
  reset_level_forces_values: assert property (
    @(posedge CLK) !RST |-> (Q == 1'b0 && QN == 1'b1)
  );

  // On a sampled falling edge of reset, outputs are 0/1.
  reset_fall_forces_values: assert property (
    @(posedge CLK) $fell(RST) |-> (Q == 1'b0 && QN == 1'b1)
  );

  // On a sampled rising edge of reset, outputs are still at reset values before capture.
  reset_rise_holds_reset_values_before_capture: assert property (
    @(posedge CLK) $rose(RST) |-> (Q == 1'b0 && QN == 1'b1)
  );

  ///// Output relationship /////
  // QN is always the logical inverse of Q.
  complement_invariant: assert property (
    @(posedge CLK) QN == ~Q
  );

  // Q and QN are never both HIGH.
  never_both_high: assert property (
    @(posedge CLK) !(Q && QN)
  );

  // Q and QN are never both LOW.
  never_both_low: assert property (
    @(posedge CLK) !(~Q && ~QN)
  );

  // A rise on Q implies a fall on QN in the same sample.
  q_rise_implies_qn_fall: assert property (
    @(posedge CLK) $rose(Q) |-> $fell(QN)
  );

  // A fall on Q implies a rise on QN in the same sample.
  q_fall_implies_qn_rise: assert property (
    @(posedge CLK) $fell(Q) |-> $rose(QN)
  );

endmodule