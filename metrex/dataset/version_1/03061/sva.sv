// Bind these SVA to the DUT
bind bitwise_logic bitwise_logic_sva sva_i (.*);

module bitwise_logic_sva (input logic A, B, input logic [1:0] SEL, input logic C);

  // Combinational sampling on any relevant change
  default clocking cb @(A or B or SEL or C); endclocking

  // Functional correctness (when operands are known)
  property p_and; (! $isunknown({A,B,SEL}) && SEL==2'b00) |-> ##0 (C === (A & B)); endproperty
  property p_or;  (! $isunknown({A,B,SEL}) && SEL==2'b01) |-> ##0 (C === (A | B)); endproperty
  property p_xor; (! $isunknown({A,B,SEL}) && SEL==2'b10) |-> ##0 (C === (A ^ B)); endproperty
  property p_not; (! $isunknown({A,SEL})   && SEL==2'b11) |-> ##0 (C === (~A));   endproperty

  a_and: assert property (p_and);
  a_or:  assert property (p_or);
  a_xor: assert property (p_xor);
  a_not: assert property (p_not);

  // Output must be known when required inputs are known
  a_known_c_logic: assert property((!$isunknown({A,B,SEL}) && SEL!=2'b11) |-> ##0 !$isunknown(C));
  a_known_c_not:   assert property((!$isunknown({A,SEL})   && SEL==2'b11) |-> ##0 !$isunknown(C));

  // B must not affect C in NOT mode
  a_not_indep_B: assert property (SEL==2'b11 && !$isunknown({A,SEL}) && $changed(B) && $stable(A) && $stable(SEL) |-> ##0 $stable(C));

  // Purely combinational: C changes only when inputs change
  a_c_only_on_input_change: assert property ($changed(C) |-> $changed({A,B,SEL}));

  // Functional coverage: exercise each op with all A/B combinations (and correct C)
  // AND
  c_and_00: cover property (SEL==2'b00 && ! $isunknown({A,B}) && A==1'b0 && B==1'b0 ##0 (C===1'b0));
  c_and_01: cover property (SEL==2'b00 && ! $isunknown({A,B}) && A==1'b0 && B==1'b1 ##0 (C===1'b0));
  c_and_10: cover property (SEL==2'b00 && ! $isunknown({A,B}) && A==1'b1 && B==1'b0 ##0 (C===1'b0));
  c_and_11: cover property (SEL==2'b00 && ! $isunknown({A,B}) && A==1'b1 && B==1'b1 ##0 (C===1'b1));

  // OR
  c_or_00: cover property (SEL==2'b01 && ! $isunknown({A,B}) && A==1'b0 && B==1'b0 ##0 (C===1'b0));
  c_or_01: cover property (SEL==2'b01 && ! $isunknown({A,B}) && A==1'b0 && B==1'b1 ##0 (C===1'b1));
  c_or_10: cover property (SEL==2'b01 && ! $isunknown({A,B}) && A==1'b1 && B==1'b0 ##0 (C===1'b1));
  c_or_11: cover property (SEL==2'b01 && ! $isunknown({A,B}) && A==1'b1 && B==1'b1 ##0 (C===1'b1));

  // XOR
  c_xor_00: cover property (SEL==2'b10 && ! $isunknown({A,B}) && A==1'b0 && B==1'b0 ##0 (C===1'b0));
  c_xor_01: cover property (SEL==2'b10 && ! $isunknown({A,B}) && A==1'b0 && B==1'b1 ##0 (C===1'b1));
  c_xor_10: cover property (SEL==2'b10 && ! $isunknown({A,B}) && A==1'b1 && B==1'b0 ##0 (C===1'b1));
  c_xor_11: cover property (SEL==2'b10 && ! $isunknown({A,B}) && A==1'b1 && B==1'b1 ##0 (C===1'b0));

  // NOT (B is don't care)
  c_not_A0: cover property (SEL==2'b11 && ! $isunknown(A) && A==1'b0 ##0 (C===1'b1));
  c_not_A1: cover property (SEL==2'b11 && ! $isunknown(A) && A==1'b1 ##0 (C===1'b0));

endmodule