// SVA checker for four_bit_adder
module four_bit_adder_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic       Cin,
  input logic [3:0] Sum,
  input logic       Cout
);
  // Clockless sampling on any change; use ##0 to avoid race with combinational updates
  default clocking cb @(*); endclocking

  // If inputs are known, outputs must be known next delta
  property p_outputs_known_when_inputs_known;
    disable iff ($isunknown({A,B,Cin}))
    ##0 !$isunknown({Sum,Cout});
  endproperty
  assert property (p_outputs_known_when_inputs_known)
    else $error("four_bit_adder: X/Z on outputs with known inputs");

  // Functional correctness: 5-bit sum equals {Cout,Sum}
  property p_full_sum_correct;
    disable iff ($isunknown({A,B,Cin}))
    ##0 {Cout,Sum} == ({1'b0,A} + {1'b0,B} + Cin);
  endproperty
  assert property (p_full_sum_correct)
    else $error("four_bit_adder: incorrect {Cout,Sum}");

  // Optional explicit carry-out check (helps debug)
  property p_cout_bit_correct;
    disable iff ($isunknown({A,B,Cin}))
    ##0 Cout == (({1'b0,A} + {1'b0,B} + Cin)[4]);
  endproperty
  assert property (p_cout_bit_correct)
    else $error("four_bit_adder: incorrect Cout");

  // Coverage: exercise Cin both values and carry-out both values
  cover property (##0 (Cin == 0));
  cover property (##0 (Cin == 1));
  cover property (##0 (({1'b0,A}+{1'b0,B}+Cin)[4] == 0));
  cover property (##0 (({1'b0,A}+{1'b0,B}+Cin)[4] == 1));

  // Extremes and representative cases
  cover property (##0 (A==4'h0 && B==4'h0 && Cin==0 && Sum==4'h0 && Cout==0));
  cover property (##0 (A==4'hF && B==4'hF && Cin==1 && Sum==4'hF && Cout==1));
  cover property (##0 (A==4'hA && B==4'h5 && Cin==0 && Sum==4'hF && Cout==0));
endmodule

// Bind into DUT
bind four_bit_adder four_bit_adder_sva sva_i (
  .A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout)
);