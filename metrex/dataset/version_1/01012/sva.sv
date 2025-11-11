// SVA for synchronous_counter
// Focus: correctness, priority, wrap, hold, and concise coverage

bind synchronous_counter synchronous_counter_checker checker_i (
  .CLK(CLK), .RST(RST), .LOAD(LOAD), .EN(EN),
  .DATA_IN(DATA_IN), .DATA_OUT(DATA_OUT)
);

module synchronous_counter_checker (
  input logic CLK, RST, LOAD, EN,
  input logic [3:0] DATA_IN,
  input logic [3:0] DATA_OUT
);

  default clocking cb @(posedge CLK); endclocking

  // Start checks after first sampled cycle to avoid $past unknowns
  bit past_valid; initial past_valid = 0;
  always @(cb) past_valid <= 1;
  default disable iff (!past_valid);

  // Priority and next-state correctness
  assert property (RST |=> DATA_OUT == 4'h0);                                   // reset wins
  assert property (!RST && LOAD |=> DATA_OUT == $past(DATA_IN));                // load when no reset
  assert property (!RST && !LOAD && EN && (DATA_OUT != 4'hF) |=>                // normal increment
                   DATA_OUT == $past(DATA_OUT) + 4'd1);
  assert property (!RST && !LOAD && EN && (DATA_OUT == 4'hF) |=>                // wrap on 0xF
                   DATA_OUT == 4'h0);
  assert property (!RST && !LOAD && !EN |=>                                     // hold when disabled
                   DATA_OUT == $past(DATA_OUT));

  // Change must be caused by some control in the previous cycle
  assert property (DATA_OUT != $past(DATA_OUT) |-> $past(RST || LOAD || EN));

  // No X/Z on DATA_OUT (after first valid cycle)
  assert property (!$isunknown(DATA_OUT));

  // Concise functional coverage
  cover property (RST ##1 DATA_OUT == 4'h0);                                    // saw reset behavior
  cover property (!RST && LOAD ##1 DATA_OUT == $past(DATA_IN));                 // saw load
  cover property (!RST && !LOAD && EN && (DATA_OUT != 4'hF) ##1                 // saw increment
                  DATA_OUT == $past(DATA_OUT) + 4'd1);
  cover property (!RST && !LOAD && EN && (DATA_OUT == 4'hF) ##1 DATA_OUT == 4'h0); // saw wrap
  cover property (!RST && !LOAD && !EN ##1 DATA_OUT == $past(DATA_OUT));        // saw hold
  cover property (RST && LOAD ##1 DATA_OUT == 4'h0);                             // priority: reset over load
  cover property (!RST && LOAD && EN ##1 DATA_OUT == $past(DATA_IN));            // priority: load over enable

endmodule