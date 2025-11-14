// SVA checker for sky130_fd_sc_hdll__o21a: X = (A1 | A2) & B1
// Focus: truth-table equivalence, 4-state robustness, and concise functional coverage.

`ifndef O21A_SVA
`define O21A_SVA

module o21a_sva (
  input logic A1,
  input logic A2,
  input logic B1,
  input logic X
);

  // Core functional equivalence when inputs are 0/1 (no X/Z)
  property p_truth_2state;
    @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge X or negedge X)
      (!$isunknown({A1,A2,B1})) |-> (X == ((A1 || A2) && B1));
  endproperty
  assert property (p_truth_2state);

  // 4-state robust implications (must hold even with X/Z on other inputs)
  // B1 low forces X low
  assert property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge X or negedge X)
                   (B1 === 1'b0) |-> (X === 1'b0));
  // If either A input is 1, X mirrors B1
  assert property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge X or negedge X)
                   ((A1 === 1'b1) || (A2 === 1'b1)) |-> (X === B1));
  // Both A inputs low force X low
  assert property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge X or negedge X)
                   ((A1 === 1'b0) && (A2 === 1'b0)) |-> (X === 1'b0));

  // If inputs are known, X must be known
  assert property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge X or negedge X)
                   (!$isunknown({A1,A2,B1})) |-> (!$isunknown(X)));

  // Sanity: X cannot change without at least one input changing (no spontaneous glitches)
  assert property (@(posedge X or negedge X) $changed({A1,A2,B1}));

  // Coverage: exercise all input combinations (2-state)
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  !$isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b000);
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  !$isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b001);
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  !$isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b010);
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  !$isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b011);
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  !$isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b100);
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  !$isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b101);
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  !$isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b110);
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  !$isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b111);

  // Coverage: observe X=0 and X=1 states
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1) X == 1'b0);
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1) X == 1'b1);

  // Coverage: key toggling scenarios that must propagate to X
  cover property (@(posedge B1) ((A1 || A2) && (X == 1'b1)));
  cover property (@(negedge B1) ((A1 || A2) && (X == 1'b0)));
  cover property (@(posedge A1) (B1 && !A2 && (X == 1'b1)));
  cover property (@(negedge A1) (B1 && !A2 && (X == 1'b0)));
  cover property (@(posedge A2) (B1 && !A1 && (X == 1'b1)));
  cover property (@(negedge A2) (B1 && !A1 && (X == 1'b0)));

endmodule

// Bind into the DUT
bind sky130_fd_sc_hdll__o21a o21a_sva o21a_sva_i (.A1(A1), .A2(A2), .B1(B1), .X(X));

`endif