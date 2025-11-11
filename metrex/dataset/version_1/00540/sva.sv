// SVA checker for adder4: functional correctness, X-checks, stability, and key corner coverage
module adder4_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       Cin,
  input  logic [3:0] S,
  input  logic       Cout
);

  // Functional correctness (combinational settle at ##0)
  property p_sum_correct;
    @(A or B or Cin or S or Cout)
      !$isunknown({A,B,Cin}) |-> ##0 ({Cout,S} === ({1'b0,A} + {1'b0,B} + Cin));
  endproperty
  assert property (p_sum_correct);

  // Outputs known when inputs known
  property p_outputs_known;
    @(A or B or Cin or S or Cout)
      !$isunknown({A,B,Cin}) |-> ##0 !$isunknown({S,Cout});
  endproperty
  assert property (p_outputs_known);

  // Combinational stability: if inputs stable, outputs do not glitch after settle
  property p_stable_when_inputs_stable;
    @(A or B or Cin or S or Cout)
      (!$isunknown({A,B,Cin}) && $stable({A,B,Cin})) |-> ##0 $stable({S,Cout});
  endproperty
  assert property (p_stable_when_inputs_stable);

  // Cin impact: rising edge increments sum by 1 if A,B stable
  property p_cin_rise_increments;
    @(A or B or Cin or S or Cout)
      (!$isunknown({A,B,Cin}) && A==$past(A) && B==$past(B) && $rose(Cin))
      |-> ##0 ({Cout,S} === $past({Cout,S}) + 5'd1);
  endproperty
  assert property (p_cin_rise_increments);

  // Cin impact: falling edge decrements sum by 1 if A,B stable
  property p_cin_fall_decrements;
    @(A or B or Cin or S or Cout)
      (!$isunknown({A,B,Cin}) && A==$past(A) && B==$past(B) && $fell(Cin))
      |-> ##0 ({Cout,S} === $past({Cout,S}) - 5'd1);
  endproperty
  assert property (p_cin_fall_decrements);

  // Commutativity over time: swapping A and B leaves result unchanged (Cin stable)
  property p_commutative;
    @(A or B or Cin or S or Cout)
      (!$isunknown({A,B,Cin}) && !$isunknown($past({A,B,Cin})) &&
       Cin==$past(Cin) && A==$past(B) && B==$past(A))
      |-> ##0 ({Cout,S} === $past({Cout,S}));
  endproperty
  assert property (p_commutative);

  // Coverage: carry-out observed
  cover property (@(A or B or Cin or S or Cout)
    !$isunknown({A,B,Cin}) ##0 (Cout==1));

  // Coverage: exact zero sum
  cover property (@(A or B or Cin or S or Cout)
    !$isunknown({A,B,Cin}) ##0 ({Cout,S}==5'd0));

  // Coverage: full propagate chain (A^B==4'hF, Cin=1 -> 0x10)
  cover property (@(A or B or Cin or S or Cout)
    (A^B)==4'hF && Cin==1 ##0 ({Cout,S}==5'h10));

  // Coverage: max+max+1 extreme
  cover property (@(A or B or Cin or S or Cout)
    A==4'hF && B==4'hF && Cin==1);

endmodule

// Bind into the DUT
bind adder4 adder4_sva i_adder4_sva (.*);