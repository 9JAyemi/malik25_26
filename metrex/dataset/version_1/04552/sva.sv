// SVA for four_bit_adder
module four_bit_adder_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic       Cin,
  input logic       CLK,
  input logic [3:0] S,
  input logic       Cout
);
  default clocking cb @(posedge CLK); endclocking

  // Functional correctness (gated for known inputs)
  property p_sum_correct;
    !$isunknown({A,B,Cin}) |-> {Cout,S} == (A + B + Cin);
  endproperty
  assert property (p_sum_correct);

  // Outputs known when inputs are known
  assert property (!$isunknown({A,B,Cin}) |-> !$isunknown({Cout,S}));

  // Stability: if inputs hold across cycles, outputs hold too
  assert property ($stable({A,B,Cin}) |-> $stable({Cout,S}));

  // Coverage: hit carry/non-carry and key edge results
  cover property (! $isunknown({A,B,Cin}) && (Cout == 0));
  cover property (! $isunknown({A,B,Cin}) && (Cout == 1));
  cover property ({Cout,S} == 5'd0);
  cover property ({Cout,S} == 5'd15);
  cover property ({Cout,S} == 5'd16);
  cover property ({Cout,S} == 5'd31);
endmodule

bind four_bit_adder four_bit_adder_sva sva_i (.*);