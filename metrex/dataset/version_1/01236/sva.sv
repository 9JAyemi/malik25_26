// SVA for dff_reset_set_ce
// Bind as: bind dff_reset_set_ce dff_reset_set_ce_sva sva(.D(D),.CLK(CLK),.RESET(RESET),.SET(SET),.CE(CE),.Q(Q),.Q_N(Q_N));

module dff_reset_set_ce_sva (
  input wire D,
  input wire CLK,
  input wire RESET,
  input wire SET,
  input wire CE,
  input wire Q,
  input wire Q_N
);
  default clocking cb @(posedge CLK); endclocking

  // Outputs are always complementary and known after first clock
  assert property ($past(1'b1) |-> (Q_N == ~Q));
  assert property ($past(1'b1) |-> (!$isunknown({Q,Q_N})));

  // Priority and next-state behavior
  assert property (RESET |-> (Q==1'b0 && Q_N==1'b1));                      // RESET wins
  assert property (!RESET && SET |-> (Q==1'b1 && Q_N==1'b0));              // SET when no RESET
  assert property (!RESET && !SET && CE |-> (Q==D && Q_N==~D));            // CE capture
  assert property (!RESET && !SET && !CE |-> (Q==$past(Q) && Q_N==$past(Q_N))); // Hold

  // Explicit overlap check (RESET over SET)
  assert property (RESET && SET |-> (Q==1'b0 && Q_N==1'b1));

  // Coverage: hit all control branches and an overlap
  cover property (RESET);
  cover property (!RESET && SET);
  cover property (!RESET && !SET && CE && (D==1'b0));
  cover property (!RESET && !SET && CE && (D==1'b1));
  cover property (!RESET && !SET && !CE);
  cover property (RESET && SET); // overlap exercised
endmodule