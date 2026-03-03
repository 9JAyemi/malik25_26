// SVA checker for mux4x1
module mux4x1_sva(
  input logic A,
  input logic B,
  input logic C,
  input logic D,
  input logic [1:0] S,
  input logic Y
);

  // Functional equivalence (4-state)
  assert property (@(*)
    Y === (S[1] ? (S[0] ? D : C) : (S[0] ? B : A))
  );

  // Correctness when all inputs/select are known (2-state check)
  assert property (@(*)
    !$isunknown({A,B,C,D,S}) |-> (Y == (S[1] ? (S[0] ? D : C) : (S[0] ? B : A)))
  );

  // Per-select mapping (also checks X-propagation from selected input)
  assert property (@(*) (S===2'b00) |-> (Y===A));
  assert property (@(*) (S===2'b01) |-> (Y===B));
  assert property (@(*) (S===2'b10) |-> (Y===C));
  assert property (@(*) (S===2'b11) |-> (Y===D));

  // Non-selected inputs do not affect Y when S is stable
  property nonsel_stable(bit [1:0] sel, logic n1, logic n2, logic n3);
    @(*) (S===sel && $stable(S) && ($changed(n1) || $changed(n2) || $changed(n3))) |-> $stable(Y);
  endproperty
  assert property (nonsel_stable(2'b00, B, C, D));
  assert property (nonsel_stable(2'b01, A, C, D));
  assert property (nonsel_stable(2'b10, A, B, D));
  assert property (nonsel_stable(2'b11, A, B, C));

  // Y follows selected input when S is stable
  property sel_follow(bit [1:0] sel, logic si);
    @(*) (S===sel && $stable(S) && $changed(si)) |-> (Y===si);
  endproperty
  assert property (sel_follow(2'b00, A));
  assert property (sel_follow(2'b01, B));
  assert property (sel_follow(2'b10, C));
  assert property (sel_follow(2'b11, D));

  // Coverage: hit each select, select switches, selected-input propagation, and immunity to non-selected changes
  cover property (@(*) S===2'b00);
  cover property (@(*) S===2'b01);
  cover property (@(*) S===2'b10);
  cover property (@(*) S===2'b11);

  cover property (@(*) !$isunknown(S) && $changed(S));

  cover property (@(*) (S===2'b00 && $stable(S) && $changed(A) && (Y===A)));
  cover property (@(*) (S===2'b01 && $stable(S) && $changed(B) && (Y===B)));
  cover property (@(*) (S===2'b10 && $stable(S) && $changed(C) && (Y===C)));
  cover property (@(*) (S===2'b11 && $stable(S) && $changed(D) && (Y===D)));

  cover property (@(*) (
      (S===2'b00 && $stable(S) && ($changed(B)||$changed(C)||$changed(D)) && $stable(Y)) ||
      (S===2'b01 && $stable(S) && ($changed(A)||$changed(C)||$changed(D)) && $stable(Y)) ||
      (S===2'b10 && $stable(S) && ($changed(A)||$changed(B)||$changed(D)) && $stable(Y)) ||
      (S===2'b11 && $stable(S) && ($changed(A)||$changed(B)||$changed(C)) && $stable(Y))
  ));

endmodule

// Bind into DUT
bind mux4x1 mux4x1_sva u_mux4x1_sva (.A(A), .B(B), .C(C), .D(D), .S(S), .Y(Y));