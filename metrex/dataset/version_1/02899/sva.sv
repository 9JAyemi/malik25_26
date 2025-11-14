// SVA for dff_preset_clear
module dff_preset_clear_sva (
  input logic D, CLK, PRE, CLR, Q, Q_N
);
  default clocking cb @(posedge CLK); endclocking

  // Basic sanity
  assert property (1 |-> !$isunknown({Q,Q_N}));        // outputs known after first cycle
  assert property (Q_N == ~Q);                          // complement relation

  // Next-cycle functional behavior (synchronous, with priority CLR > PRE > D)
  assert property (CLR              |=> Q == 1'b0);
  assert property (!CLR && PRE      |=> Q == 1'b1);
  assert property (!CLR && !PRE     |=> Q == $past(D));
  assert property (CLR && PRE       |=> Q == 1'b0);     // explicit priority when both set

  // Functional coverage
  cover  property (CLR);
  cover  property (!CLR && PRE);
  cover  property (!CLR && !PRE);
  cover  property (CLR && PRE);
  cover  property (!CLR && !PRE && D != $past(D) |=> Q != $past(Q)); // Q follows D toggle
  cover  property ($rose(Q));
  cover  property ($fell(Q));
endmodule

bind dff_preset_clear dff_preset_clear_sva sva_i(
  .D(D), .CLK(CLK), .PRE(PRE), .CLR(CLR), .Q(Q), .Q_N(Q_N)
);