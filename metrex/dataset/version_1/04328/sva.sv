// SVA for sky130_fd_sc_hdll__o221a
// Function: X = (B1|B2) & (A1|A2) & C1

// Bind module
module sky130_fd_sc_hdll__o221a_sva (
  input logic A1, A2, B1, B2, C1,
  input logic X,
  input logic or0_out, or1_out, and0_out_X
);

  // Any input edge
  `define ANY_IN_EDGES  (posedge A1 or negedge A1 or \
                         posedge A2 or negedge A2 or \
                         posedge B1 or negedge B1 or \
                         posedge B2 or negedge B2 or \
                         posedge C1 or negedge C1)

  // Core functional equivalence (evaluate after delta to avoid races)
  property p_func;
    @(`ANY_IN_EDGES) disable iff ($isunknown({A1,A2,B1,B2,C1}))
      1 |-> ##0 (X === ((B1 | B2) & (A1 | A2) & C1));
  endproperty
  assert property (p_func);

  // Internal net checks
  property p_or0;
    @(`ANY_IN_EDGES) disable iff ($isunknown({B1,B2}))
      1 |-> ##0 (or0_out === (B1 | B2));
  endproperty
  assert property (p_or0);

  property p_or1;
    @(`ANY_IN_EDGES) disable iff ($isunknown({A1,A2}))
      1 |-> ##0 (or1_out === (A1 | A2));
  endproperty
  assert property (p_or1);

  property p_and0;
    @(`ANY_IN_EDGES) disable iff ($isunknown({or0_out,or1_out,C1}))
      1 |-> ##0 (and0_out_X === (or0_out & or1_out & C1));
  endproperty
  assert property (p_and0);

  property p_buf;
    @(`ANY_IN_EDGES)
      1 |-> ##0 (X === and0_out_X);
  endproperty
  assert property (p_buf);

  // Strong implications (must always hold, even with X/Z on unrelated inputs)
  // C1 low forces X low
  assert property (@(posedge C1 or negedge C1) (!C1) |-> ##0 (X == 1'b0));
  // Both A low forces X low
  assert property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2)
                    (!A1 && !A2) |-> ##0 (X == 1'b0));
  // Both B low forces X low
  assert property (@(posedge B1 or negedge B1 or posedge B2 or negedge B2)
                    (!B1 && !B2) |-> ##0 (X == 1'b0));
  // If X is high, all three factors must be high
  assert property (@(`ANY_IN_EDGES) X |-> (C1 && (A1 || A2) && (B1 || B2)));

  // Coverage: exercise both polarities and minimal enabling combinations
  cover property (@(posedge X) 1);
  cover property (@(negedge X) 1);

  // Four minimal asserts with C1=1
  cover property (@(`ANY_IN_EDGES) ##0 (C1 &&  A1 && !A2 &&  B1 && !B2 && X));
  cover property (@(`ANY_IN_EDGES) ##0 (C1 &&  A1 && !A2 && !B1 &&  B2 && X));
  cover property (@(`ANY_IN_EDGES) ##0 (C1 && !A1 &&  A2 &&  B1 && !B2 && X));
  cover property (@(`ANY_IN_EDGES) ##0 (C1 && !A1 &&  A2 && !B1 &&  B2 && X));

  // Coverage: common X==0 reasons
  cover property (@(`ANY_IN_EDGES) ##0 (!C1 && (X == 1'b0)));
  cover property (@(`ANY_IN_EDGES) ##0 (C1 && (!A1 && !A2) && (X == 1'b0)));
  cover property (@(`ANY_IN_EDGES) ##0 (C1 && (!B1 && !B2) && (X == 1'b0)));

  `undef ANY_IN_EDGES
endmodule

// Bind into all instances of the DUT
bind sky130_fd_sc_hdll__o221a sky130_fd_sc_hdll__o221a_sva
  u_o221a_sva (
    .A1(A1), .A2(A2), .B1(B1), .B2(B2), .C1(C1),
    .X(X),
    .or0_out(or0_out), .or1_out(or1_out), .and0_out_X(and0_out_X)
  );