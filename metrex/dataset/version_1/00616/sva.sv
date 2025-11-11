// SVA for nor4_gate
module nor4_gate_sva (
    input logic A, B, C, D,
    input logic Y
);

  // Helpers for 4-state reasoning
  wire any1 = (A===1'b1) || (B===1'b1) || (C===1'b1) || (D===1'b1);
  wire all0 = (A===1'b0) && (B===1'b0) && (C===1'b0) && (D===1'b0);

  // Functional equivalence (handles X/Z via 4-state operators)
  property p_func;
    @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
      1 |-> ##0 (Y === ~(A|B|C|D));
  endproperty
  assert property (p_func)
    else $error("NOR4 mismatch: Y=%b A=%b B=%b C=%b D=%b", Y,A,B,C,D);

  // Strengthened checks (deterministic cases and X-prop)
  property p_all0_1;
    @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
      all0 |-> ##0 (Y === 1'b1);
  endproperty
  assert property (p_all0_1);

  property p_any1_0;
    @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
      any1 |-> ##0 (Y === 1'b0);
  endproperty
  assert property (p_any1_0);

  property p_xprop;
    @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
      (!any1 && !all0) |-> ##0 $isunknown(Y);
  endproperty
  assert property (p_xprop);

  // Full 2-state truth-table coverage (all 16 input combos)
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D) {A,B,C,D,Y} == 5'b00001);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D) {A,B,C,D,Y} == 5'b00010);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D) {A,B,C,D,Y} == 5'b00100);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D) {A,B,C,D,Y} == 5'b00110);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D) {A,B,C,D,Y} == 5'b01000);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D) {A,B,C,D,Y} == 5'b01010);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D) {A,B,C,D,Y} == 5'b01100);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D) {A,B,C,D,Y} == 5'b01110);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D) {A,B,C,D,Y} == 5'b10000);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D) {A,B,C,D,Y} == 5'b10010);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D) {A,B,C,D,Y} == 5'b10100);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D) {A,B,C,D,Y} == 5'b10110);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D) {A,B,C,D,Y} == 5'b11000);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D) {A,B,C,D,Y} == 5'b11010);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D) {A,B,C,D,Y} == 5'b11100);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D) {A,B,C,D,Y} == 5'b11110);

endmodule

// Bind into DUT
bind nor4_gate nor4_gate_sva nor4_gate_sva_i (.A(A), .B(B), .C(C), .D(D), .Y(Y));