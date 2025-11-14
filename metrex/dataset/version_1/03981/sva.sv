// SVA checker for dff_en_rst
module dff_en_rst_sva (input logic D, C, E, R, Q);

  // Use posedge C as sampling clock
  default clocking cb @(posedge C); endclocking

  // Guard $past usage on first active clock
  bit past_valid;
  always_ff @(posedge C) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Core behavior mirrors RTL priority:
  // 1) synchronous active-low reset
  // 2) enable load
  // 3) otherwise hold

  // 1) Reset dominates: if R===0, next Q must be 0
  property p_reset_forces_zero;
    (R === 1'b0) |=> (Q === 1'b0);
  endproperty
  assert property (p_reset_forces_zero);

  // 2) Enabled load when not in reset: if R!==0 and E===1, next Q == sampled D
  property p_enable_loads_d;
    (R !== 1'b0 && E === 1'b1) |=> (Q === $past(D));
  endproperty
  assert property (p_enable_loads_d);

  // 3) Hold otherwise: if R!==0 and E!==1, no assignment, so Q holds
  property p_hold_when_not_loading;
    (R !== 1'b0 && E !== 1'b1) |=> (Q === $past(Q));
  endproperty
  assert property (p_hold_when_not_loading);

  // Optional sanity: Q only changes due to the clocked logic (no async glitches between clocks)
  // This is implied by the three assertions above, but we also ensure Q does not change
  // on the falling edge sample as a lightweight check.
  assert property (@(negedge C) !$changed(Q));

  // ----------------
  // Functional coverage
  // ----------------

  // Cover reset taking effect
  cover property (p_reset_forces_zero);

  // Cover enabled load of 0 and 1
  cover property ((R !== 1'b0 && E === 1'b1 && D === 1'b0) |=> (Q === 1'b0));
  cover property ((R !== 1'b0 && E === 1'b1 && D === 1'b1) |=> (Q === 1'b1));

  // Cover hold
  cover property ((R !== 1'b0 && E !== 1'b1) |=> (Q === $past(Q)));

  // Cover reset dominating even when E===1
  cover property ((R === 1'b0 && E === 1'b1) |=> (Q === 1'b0));

  // Cover a toggle due to enabled load
  cover property ((R !== 1'b0 && E === 1'b1 && D !== $past(Q)) |=> (Q !== $past(Q)));

endmodule

// Bind into the DUT
bind dff_en_rst dff_en_rst_sva u_dff_en_rst_sva (.*);