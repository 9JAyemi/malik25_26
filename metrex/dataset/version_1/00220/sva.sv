// SVA for sffsrce_fdre and FFAR

module sffsrce_fdre_sva (input Q, C, CE, D, R, SET, RESET);
  default clocking cb @(posedge C); endclocking
  logic past_valid; initial past_valid = 1'b0; always @(posedge C) past_valid <= 1'b1;

  // Priority and function
  a_set:   assert property (disable iff (!past_valid)  CE && SET                           |=> Q == 1'b1);
  a_reset: assert property (disable iff (!past_valid)  CE && !SET && RESET                 |=> Q == 1'b0);
  a_load:  assert property (disable iff (!past_valid)  CE && !SET && !RESET && R           |=> Q == $past(D));
  a_hold1: assert property (disable iff (!past_valid)  CE && !SET && !RESET && !R          |=> Q == $past(Q));
  a_hold0: assert property (disable iff (!past_valid) !CE                                   |=> Q == $past(Q));

  // No unintended updates between edges
  a_no_negedge_change: assert property (disable iff (!past_valid) @(negedge C) $stable(Q));

  // Coverage
  c_set:            cover property (CE && SET);
  c_reset:          cover property (CE && !SET && RESET);
  c_load0:          cover property (CE && !SET && !RESET && R && D==1'b0);
  c_load1:          cover property (CE && !SET && !RESET && R && D==1'b1);
  c_hold_ce1:       cover property (CE && !SET && !RESET && !R);
  c_hold_ce0:       cover property (!CE);
  c_set_over_reset: cover property (CE && SET && RESET);
  c_r_masked_reset: cover property (CE && !SET && RESET && R);
endmodule

bind sffsrce_fdre sffsrce_fdre_sva (.Q(Q), .C(C), .CE(CE), .D(D), .R(R), .SET(SET), .RESET(RESET));

module FFAR_sva (input Q, C, CE, D, R);
  default clocking cb @(posedge C); endclocking
  logic past_valid; initial past_valid = 1'b0; always @(posedge C) past_valid <= 1'b1;

  // Wrapper behavior (SET/RESET tied low)
  a_load: assert property (disable iff (!past_valid)  CE && R                  |=> Q == $past(D));
  a_hold: assert property (disable iff (!past_valid) (!CE) || (CE && !R)       |=> Q == $past(Q));

  // Constants inside wrapper
  a_S_tied_low: assert property (disable iff (!past_valid) S == 1'b0);

  // No unintended updates between edges
  a_no_negedge_change: assert property (disable iff (!past_valid) @(negedge C) $stable(Q));

  // Coverage
  c_load0:    cover property (CE && R && D==1'b0);
  c_load1:    cover property (CE && R && D==1'b1);
  c_hold_ce0: cover property (!CE);
  c_hold_ce1: cover property (CE && !R);
  c_q_tog:    cover property (CE && R && D != $past(Q));
endmodule

bind FFAR FFAR_sva (.Q(Q), .C(C), .CE(CE), .D(D), .R(R));