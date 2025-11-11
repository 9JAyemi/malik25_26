// SVA checker for my_circuit
module my_circuit_sva (
  input logic A1, A2, B1, C1,
  input logic Y,
  input logic VPWR, VGND, VPB, VNB
);

  // Power must be valid and static
  property p_supplies_const;
    @(*) (VPWR===1'b1) && (VGND===1'b0) && (VPB===1'b1) && (VNB===1'b0);
  endproperty
  assert property (p_supplies_const);

  // 4-state functional equivalence (includes X/Z semantics)
  property p_func_equiv_4state;
    @(*) Y === ((A1 & A2) & (B1 | C1));
  endproperty
  assert property (p_func_equiv_4state);

  // When inputs are known (and power good), output must be known and 2-state correct
  logic pgood;
  assign pgood = (VPWR===1'b1) && (VGND===1'b0) && (VPB===1'b1) && (VNB===1'b0);

  property p_no_x_on_y_when_inputs_known;
    @(*) pgood && !$isunknown({A1,A2,B1,C1}) |-> !$isunknown(Y);
  endproperty
  assert property (p_no_x_on_y_when_inputs_known);

  property p_func_equiv_2state_when_known;
    @(*) pgood && !$isunknown({A1,A2,B1,C1}) |-> (Y == ((A1 & A2) & (B1 | C1)));
  endproperty
  assert property (p_func_equiv_2state_when_known);

  // No spurious Y change without an input change (under good power, known states)
  property p_no_spurious_y_change;
    @(*) pgood && !$isunknown({A1,A2,B1,C1,Y}) && $changed(Y) |-> $changed({A1,A2,B1,C1});
  endproperty
  assert property (p_no_spurious_y_change);

  // Coverage: observe output values and transitions
  cover property (@(*) Y==1'b1);
  cover property (@(*) Y==1'b0);
  cover property (@(*) $rose(Y));
  cover property (@(*) $fell(Y));

  // Coverage: all 16 input combinations
  cover property (@(*) {A1,A2,B1,C1} == 4'b0000);
  cover property (@(*) {A1,A2,B1,C1} == 4'b0001);
  cover property (@(*) {A1,A2,B1,C1} == 4'b0010);
  cover property (@(*) {A1,A2,B1,C1} == 4'b0011);
  cover property (@(*) {A1,A2,B1,C1} == 4'b0100);
  cover property (@(*) {A1,A2,B1,C1} == 4'b0101);
  cover property (@(*) {A1,A2,B1,C1} == 4'b0110);
  cover property (@(*) {A1,A2,B1,C1} == 4'b0111);
  cover property (@(*) {A1,A2,B1,C1} == 4'b1000);
  cover property (@(*) {A1,A2,B1,C1} == 4'b1001);
  cover property (@(*) {A1,A2,B1,C1} == 4'b1010);
  cover property (@(*) {A1,A2,B1,C1} == 4'b1011);
  cover property (@(*) {A1,A2,B1,C1} == 4'b1100);
  cover property (@(*) {A1,A2,B1,C1} == 4'b1101);
  cover property (@(*) {A1,A2,B1,C1} == 4'b1110);
  cover property (@(*) {A1,A2,B1,C1} == 4'b1111);

endmodule

// Bind into the DUT
bind my_circuit my_circuit_sva my_circuit_sva_i(.*);