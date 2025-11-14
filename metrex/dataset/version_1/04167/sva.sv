// SVA for LedPWM
// Bind into DUT to check functionality and provide focused coverage.

module LedPWM_sva(
  input logic              clk,
  input logic [7:0]        value,
  input logic              out,
  input logic [7:0]        PWMCounter,
  input logic              outreg
);
  default clocking cb @(posedge clk); endclocking
  default disable iff ($isunknown({clk,value,PWMCounter,outreg,out}));

  // Structural/legal checks
  ap_out_is_outreg:      assert property (out === outreg);
  ap_cnt_increments:     assert property (!$isunknown($past(PWMCounter)) |-> PWMCounter == $past(PWMCounter) + 8'd1);

  // Functional checks (as coded, including operator precedence)
  ap_out_logic_precise:  assert property (out == (PWMCounter <= (value & (value != 0))));

  // Useful behavioral checks derived from coded logic
  ap_value_zero_low:     assert property ((value == 8'd0) |-> !out);
  ap_even_nonzero:       assert property ((value != 0 && ~value[0]) |-> (out == (PWMCounter == 8'd0)));
  ap_odd_nonzero:        assert property ((value != 0 &&  value[0]) |-> (out == (PWMCounter inside {8'd0,8'd1})));

  // Coverage
  cp_cnt_wrap:           cover  property ($past(PWMCounter) == 8'hFF && PWMCounter == 8'h00);
  cp_even_pulse:         cover  property (value != 0 && ~value[0] && PWMCounter == 8'd0 && out);
  cp_odd_two_pulses:     cover  property (value != 0 && value[0] && PWMCounter == 8'd0 && out ##1 value != 0 && value[0] && PWMCounter == 8'd1 && out);

  // Coverage to highlight possible operator-precedence ambiguity vs intended behavior
  cp_precedence_diff:    cover  property (((PWMCounter <= value) & (value != 0)) != (PWMCounter <= (value & (value != 0))));
endmodule

bind LedPWM LedPWM_sva sva(.clk(clk), .value(value), .out(out), .PWMCounter(PWMCounter), .outreg(outreg));