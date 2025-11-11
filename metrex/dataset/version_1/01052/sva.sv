// SVA for full_adder and four_bit_adder
// Bind these into the DUT; no TB modifications required.

module full_adder_sva (
  input A, input B, input Cin,
  input S, input Cout
);

  // Functional correctness (combinational, sampled after delta cycle)
  property fa_func;
    @(posedge A or negedge A or
      posedge B or negedge B or
      posedge Cin or negedge Cin)
      !$isunknown({A,B,Cin}) |-> ##0
        ( S    == (A ^ B ^ Cin) &&
          Cout == ((A & B) | (Cin & (A ^ B))) );
  endproperty
  assert property (fa_func);

  // Known inputs imply known outputs
  property fa_known_out;
    @(posedge A or negedge A or
      posedge B or negedge B or
      posedge Cin or negedge Cin)
      !$isunknown({A,B,Cin}) |-> ##0 !$isunknown({S,Cout});
  endproperty
  assert property (fa_known_out);

  // Cover all 8 input combinations (per instance)
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge Cin or negedge Cin)
                  !$isunknown({A,B,Cin}) && {A,B,Cin} == 3'b000);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge Cin or negedge Cin)
                  !$isunknown({A,B,Cin}) && {A,B,Cin} == 3'b001);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge Cin or negedge Cin)
                  !$isunknown({A,B,Cin}) && {A,B,Cin} == 3'b010);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge Cin or negedge Cin)
                  !$isunknown({A,B,Cin}) && {A,B,Cin} == 3'b011);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge Cin or negedge Cin)
                  !$isunknown({A,B,Cin}) && {A,B,Cin} == 3'b100);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge Cin or negedge Cin)
                  !$isunknown({A,B,Cin}) && {A,B,Cin} == 3'b101);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge Cin or negedge Cin)
                  !$isunknown({A,B,Cin}) && {A,B,Cin} == 3'b110);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge Cin or negedge Cin)
                  !$isunknown({A,B,Cin}) && {A,B,Cin} == 3'b111);

endmodule

bind full_adder full_adder_sva fa_sva_i (.*);

module four_bit_adder_sva (
  input  [3:0] A, input [3:0] B, input Cin,
  input  [3:0] S, input Cout
);

  // Convenience event: any input edge (expanded explicitly)
  // Functional correctness: full 5-bit sum
  property fba_sum_ok;
    @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or
      posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
      posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or
      posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
      posedge Cin  or negedge Cin)
      !$isunknown({A,B,Cin}) |-> ##0 ({Cout,S} == (A + B + Cin));
  endproperty
  assert property (fba_sum_ok);

  // Known inputs imply known outputs
  property fba_known_out;
    @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or
      posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
      posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or
      posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
      posedge Cin  or negedge Cin)
      !$isunknown({A,B,Cin}) |-> ##0 !$isunknown({S,Cout});
  endproperty
  assert property (fba_known_out);

  // All-propagate path: A^B=4'hF propagates Cin through carry; S mirrors ~Cin
  property fba_all_propagate;
    @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or
      posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
      posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or
      posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
      posedge Cin  or negedge Cin)
      (!$isunknown({A,B,Cin}) && ((A ^ B) == 4'hF)) |-> ##0
        (Cout == Cin && S == {4{~Cin}});
  endproperty
  assert property (fba_all_propagate);

  // MSB generate must force Cout irrespective of lower bits/Cin
  property fba_msb_generate;
    @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or
      posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
      posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or
      posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
      posedge Cin  or negedge Cin)
      (!$isunknown({A,B,Cin}) && (A[3] & B[3])) |-> ##0 (Cout == 1'b1);
  endproperty
  assert property (fba_msb_generate);

  // Targeted coverage
  cover property (@(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or
                    posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
                    posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or
                    posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
                    posedge Cin  or negedge Cin)
                   (A==4'h0 && B==4'h0 && Cin==1'b0 && S==4'h0 && Cout==1'b0));

  cover property (@(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or
                    posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
                    posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or
                    posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
                    posedge Cin  or negedge Cin)
                   (A==4'hF && B==4'hF && Cin==1'b1 && S==4'h0 && Cout==1'b1));

  cover property (@(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or
                    posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
                    posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or
                    posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
                    posedge Cin  or negedge Cin)
                   ((A^B)==4'hF && Cin==1'b0 && S==4'hF && Cout==1'b0));

  cover property (@(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or
                    posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
                    posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or
                    posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
                    posedge Cin  or negedge Cin)
                   ((A^B)==4'hF && Cin==1'b1 && S==4'h0 && Cout==1'b1));

  cover property (@(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or
                    posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
                    posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or
                    posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
                    posedge Cin  or negedge Cin)
                   (!$isunknown({A,B,Cin,S,Cout}) && (Cout==1'b0)));

  cover property (@(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or
                    posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
                    posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or
                    posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
                    posedge Cin  or negedge Cin)
                   (!$isunknown({A,B,Cin,S,Cout}) && (Cout==1'b1)));

endmodule

bind four_bit_adder four_bit_adder_sva fba_sva_i (.*);