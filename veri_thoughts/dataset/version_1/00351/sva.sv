// SVA for nfa_accept_samples_generic_hw_mul_8ns_6ns_14_2_MAC2S_1
module nfa_accept_samples_generic_hw_mul_8ns_6ns_14_2_MAC2S_1_sva
(
  input logic                     clk,
  input logic                     ce,
  input logic [8-1:0]             a,
  input logic [6-1:0]             b,
  input logic [14-1:0]            p
);

  default clocking cb @(posedge clk); endclocking

  // When ce is 1, next cycle p must equal a*b from this cycle; require known a,b.
  assert property ( disable iff ($initstate)
    (ce && !$isunknown({a,b})) |-> (p == $past(a*b) && !$isunknown(p))
  );

  // When ce is 0, p must hold its previous value (after first sampled cycle).
  assert property ( disable iff ($initstate || $isunknown($past(p)))
    (ce == 1'b0) |-> (p == $past(p))
  );

  // Optional sanity: zero operand implies zero product on next cycle when captured.
  assert property ( disable iff ($initstate)
    (ce && (a == 0 || b == 0)) |-> (p == 14'd0)
  );

  // Optional sanity: max operands produce expected max product when captured.
  assert property ( disable iff ($initstate)
    (ce && a == 8'hFF && b == 6'h3F) |-> (p == 14'd16065)
  );

  // Inputs must be known when capturing.
  assert property ( disable iff ($initstate)
    ce |-> !$isunknown({a,b,ce})
  );

  // Coverage: capture occurs, back-to-back captures, zero and max cases, idle streak.
  cover property (ce);
  cover property (ce && $past(ce));
  cover property (ce && (a == 0 || b == 0));
  cover property (ce && a == 8'hFF && b == 6'h3F);
  cover property ((!ce)[*3]);

endmodule

// Bind into DUT
bind nfa_accept_samples_generic_hw_mul_8ns_6ns_14_2_MAC2S_1
  nfa_accept_samples_generic_hw_mul_8ns_6ns_14_2_MAC2S_1_sva sva_inst (.*);