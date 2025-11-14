// SVA for dff_async_reset_set_enable (bind into DUT)

bind dff_async_reset_set_enable dff_async_reset_set_enable_sva i_dff_async_reset_set_enable_sva (
  .CLK(CLK), .RESET(RESET), .SET(SET), .EN(EN), .D(D), .Q(Q), .QBAR(QBAR), .R(R)
);

module dff_async_reset_set_enable_sva (
  input logic CLK, RESET, SET, EN, D,
  input logic Q, QBAR,
  input logic R
);

  default clocking cb @(posedge CLK); endclocking

  // past-valid guard
  logic past_valid;
  initial past_valid = 0;
  always @(posedge CLK) past_valid <= 1'b1;

  // Functional next-state check (synchronous, priority RESET > SET > EN)
  a_func: assert property (disable iff (!past_valid)
                           Q == (RESET ? 1'b0 :
                                 SET   ? 1'b1 :
                                 EN    ? D     :
                                         $past(Q)));

  // Complementary outputs must always match
  a_comp: assert property (QBAR == ~Q);

  // No X/Z on outputs at clock boundaries
  a_no_x: assert property (!$isunknown({Q, QBAR}));

  // R as implemented should be 0 after each clock (catches ineffective gating)
  a_R_zero: assert property (1'b1 |=> R == 1'b0);

  // Optional: outputs do not toggle on the falling edge
  a_no_negedge_change: assert property (@(negedge CLK) $stable({Q, QBAR}));

  // Coverage: hit all control paths and priority
  c_reset:  cover property (RESET);
  c_set:    cover property (!RESET && SET);
  c_en0:    cover property (!RESET && !SET && EN && D == 1'b0);
  c_en1:    cover property (!RESET && !SET && EN && D == 1'b1);
  c_hold:   cover property (!RESET && !SET && !EN);
  c_both:   cover property (RESET && SET); // demonstrate RESET priority

endmodule