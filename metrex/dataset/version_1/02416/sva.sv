// SVA for four_bit_adder. Bind this to the DUT.
module four_bit_adder_sva(
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       Cin,
  input  logic [3:0] Sum,
  input  logic       Cout
);

  // Primary functional correctness with X-guard and delta-cycle settle
  property p_inputs_known; !$isunknown({A,B,Cin}); endproperty
  assert property (@(A or B or Cin)
                   p_inputs_known |-> ##0 (!$isunknown({Cout,Sum}) &&
                                            {Cout,Sum} == A + B + Cin))
    else $error("Adder mismatch/X: A=%0h B=%0h Cin=%0b -> Sum=%0h Cout=%0b (exp=%0h)",
                A,B,Cin,Sum,Cout, A+B+Cin);

  // Useful derived check: full propagate condition (A^B)==4'hF implies Cout==Cin
  assert property (@(A or B or Cin)
                   p_inputs_known && ((A^B)==4'hF) |-> ##0 (Cout == Cin))
    else $error("Propagate property violated: A=%0h B=%0h Cin=%0b Cout=%0b", A,B,Cin,Cout);

  // Coverage: exercise carries, extremes, and propagate paths
  cover property (@(A or B or Cin) p_inputs_known ##0 (Cout==0));
  cover property (@(A or B or Cin) p_inputs_known ##0 (Cout==1));
  cover property (@(A or B or Cin) p_inputs_known ##0 (Sum==4'h0));
  cover property (@(A or B or Cin) p_inputs_known ##0 (Sum==4'hF));
  cover property (@(A or B or Cin) (A==4'h0 && B==4'h0 && Cin==1'b0) ##0 (Sum==4'h0 && Cout==1'b0));
  cover property (@(A or B or Cin) (A==4'hF && B==4'hF && Cin==1'b1) ##0 (Sum==4'hF && Cout==1'b1));
  cover property (@(A or B or Cin) p_inputs_known && ((A^B)==4'hF) && (Cin==1'b0) ##0 (Cout==1'b0));
  cover property (@(A or B or Cin) p_inputs_known && ((A^B)==4'hF) && (Cin==1'b1) ##0 (Cout==1'b1));

endmodule

bind four_bit_adder four_bit_adder_sva sva_i(.*);