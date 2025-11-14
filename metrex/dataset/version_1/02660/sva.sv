// Bind these assertions to every adder_4bit instance
bind adder_4bit adder_4bit_sva();

module adder_4bit_sva;

  // Functional correctness on any input change; allow delta-cycle settle (##0)
  property p_sum_correct;
    @(A or B or Cin)
      !$isunknown({A,B,Cin}) |-> ##0 {Cout,S} == ({1'b0,A} + {1'b0,B} + Cin);
  endproperty
  assert property (p_sum_correct);

  // Outputs must be known when inputs are known
  assert property (@(A or B or Cin)
    !$isunknown({A,B,Cin}) |-> ##0 !$isunknown({S,Cout})
  );

  // Internal consistency checks
  assert property (@(A or B or Cin)
    1 |-> ##0 Sum == ({1'b0,A} + {1'b0,B} + Cin)
  );
  assert property (@(A or B or Cin)
    1 |-> ##0 (S == Sum[3:0]) && (Cout == Sum[4])
  );

  // Coverage: key scenarios and corner cases
  cover property (@(A or B or Cin) ##0 {Cout,S} == 5'h00);                   // 0+0+0
  cover property (@(A or B or Cin) ##0 (!Cout && S == 4'hF));                // max sum without carry
  cover property (@(A or B or Cin) (A==4'hF && B==4'h1 && Cin==1'b0) ##0 (S==4'h0 && Cout==1'b1)); // overflow without Cin
  cover property (@(A or B or Cin) (A==4'hF && B==4'h0 && Cin==1'b1) ##0 (S==4'h0 && Cout==1'b1)); // overflow from Cin
  cover property (@(A or B or Cin) ##0 (Cout==1'b0));                        // observe no-carry cases
  cover property (@(A or B or Cin) ##0 (Cout==1'b1));                        // observe carry-out cases
  cover property (@(A or B or Cin) (A==4'h0 && B==4'h0 && Cin==1'b0));       // input all-zero hit

endmodule