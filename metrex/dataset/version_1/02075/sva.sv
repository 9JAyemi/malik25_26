// SVA for ResetInverter: RESET_OUT must be logical negation of RESET_IN

module ResetInverter_sva(input logic RESET_IN, input logic RESET_OUT);

  // Core functional check; ##0 avoids preponed-region race
  property p_inversion;
    @(RESET_IN or RESET_OUT) ##0 (RESET_OUT === !RESET_IN);
  endproperty
  a_inversion: assert property (p_inversion);

  // If input is known (0/1), output must be known in the same time slot
  property p_no_x_when_input_known;
    @(RESET_IN) (!$isunknown(RESET_IN)) |-> ##0 (!$isunknown(RESET_OUT));
  endproperty
  a_no_x_when_input_known: assert property (p_no_x_when_input_known);

  // Coverage: both steady states, both edges, and X-propagation
  c_low_state:  cover property (@(RESET_IN or RESET_OUT) ##0 (!RESET_IN && RESET_OUT));
  c_high_state: cover property (@(RESET_IN or RESET_OUT) ##0 (RESET_IN && !RESET_OUT));
  c_posedge:    cover property (@(posedge RESET_IN)      ##0 (RESET_OUT == 1'b0));
  c_negedge:    cover property (@(negedge RESET_IN)      ##0 (RESET_OUT == 1'b1));
  c_unknown:    cover property (@(RESET_IN or RESET_OUT) ##0 ($isunknown(RESET_IN) && $isunknown(RESET_OUT)));

endmodule

bind ResetInverter ResetInverter_sva sva(.RESET_IN(RESET_IN), .RESET_OUT(RESET_OUT));