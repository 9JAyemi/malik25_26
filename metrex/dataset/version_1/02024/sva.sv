// SVA checker for NOR3X1
// Bind this into the DUT: bind NOR3X1 NOR3X1_sva u_NOR3X1_sva (.*);

module NOR3X1_sva (
  input logic A, B, C,
  input logic Y,
  input logic AB_nor,
  input logic AB_nor_C_nor
);
  // Sample on any combinational change
  event comb_ev;
  always @* -> comb_ev;

  // Structural correctness of internal gates and connection to Y
  assert property (@(comb_ev) AB_nor            === ~(A | B))
    else $error("AB_nor must be ~(A|B)");
  assert property (@(comb_ev) AB_nor_C_nor      === ~(AB_nor | C))
    else $error("AB_nor_C_nor must be ~(AB_nor|C)");
  assert property (@(comb_ev) Y                 === AB_nor_C_nor)
    else $error("Y must be driven by AB_nor_C_nor");

  // High-level functional spec for NOR3: Y == ~(A|B|C)
  // This will flag if implementation deviates from true 3-input NOR
  assert property (@(comb_ev) Y === ~(A | B | C))
    else $error("Functional mismatch: Y != ~(A|B|C)");

  // X-propagation sanity: if inputs are known, output must be known
  assert property (@(comb_ev) (!$isunknown({A,B,C})) |-> !$isunknown(Y))
    else $error("Y is X/Z while inputs are all known");

  // Functional coverage
  // Cover all input combinations
  cover property (@(comb_ev) {A,B,C} == 3'b000);
  cover property (@(comb_ev) {A,B,C} == 3'b001);
  cover property (@(comb_ev) {A,B,C} == 3'b010);
  cover property (@(comb_ev) {A,B,C} == 3'b011);
  cover property (@(comb_ev) {A,B,C} == 3'b100);
  cover property (@(comb_ev) {A,B,C} == 3'b101);
  cover property (@(comb_ev) {A,B,C} == 3'b110);
  cover property (@(comb_ev) {A,B,C} == 3'b111);

  // Cover both output polarities
  cover property (@(comb_ev) Y == 1'b0);
  cover property (@(comb_ev) Y == 1'b1);

  // Spec-oriented coverage: expected NOR3 truth points
  cover property (@(comb_ev) (~(A|B|C)) && (Y === 1'b1)); // all-zero inputs -> Y=1
  cover property (@(comb_ev)  (A|B|C)   && (Y === 1'b0)); // any-one input -> Y=0
endmodule