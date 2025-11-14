// SVA for single_module: T-enabled TFF with no reset
module single_module_sva (input logic C, T, E, Q, xorout);

  // Track we've seen at least one posedge C
  bit seen_clk;
  initial seen_clk = 1'b0;
  always @(posedge C) seen_clk <= 1'b1;

  default clocking cb @(posedge C); endclocking

  // Basic sanity/known checks
  assert property (cb !$isunknown({T,E}));                       // inputs known on clock
  assert property (cb seen_clk |-> !$isunknown(Q));              // Q known after first edge
  assert property (cb xorout == (T ^ Q));                        // combinational xorout correctness

  // Next-state function: Q(next) = Q ^ (E & T)
  property p_next_state;
    logic q0, t0, e0;
    (q0 = Q, t0 = T, e0 = E) |=> (Q == (q0 ^ (e0 & t0)));
  endproperty
  assert property (cb p_next_state);

  // Toggle occurs iff E & T is 1
  property p_must_toggle_when_ET;
    logic q0;
    (q0 = Q, E && T) |=> (Q != q0);
  endproperty
  assert property (cb p_must_toggle_when_ET);

  property p_no_toggle_when_not_ET;
    logic q0;
    (q0 = Q, !(E && T)) |=> (Q == q0);
  endproperty
  assert property (cb p_no_toggle_when_not_ET);

  // Glitchless: Q does not change between clock edges
  assert property (@(negedge C) seen_clk |-> (Q == $past(Q, 1, posedge C)));

  // Functional coverage
  cover property (cb (Q==0, E && T) |=> (Q==1));   // 0->1 toggle
  cover property (cb (Q==1, E && T) |=> (Q==0));   // 1->0 toggle
  cover property (cb (logic q0; q0=Q, !E)        |=> (Q==q0)); // hold when E=0
  cover property (cb (logic q0; q0=Q, E && !T)   |=> (Q==q0)); // hold when E=1,T=0
endmodule

bind single_module single_module_sva i_single_module_sva (.C(C), .T(T), .E(E), .Q(Q), .xorout(xorout));