// SVA checker for full_adder
module full_adder_sva(input logic A, B, Cin, S, Cout);

  // Functional correctness (guarded against unknown inputs)
  a_sum:  assert property (@(A or B or Cin)
            !$isunknown({A,B,Cin}) |-> ##0
            ({Cout,S} == ({1'b0,A}+{1'b0,B}+{1'b0,Cin}))
          );

  a_sxor: assert property (@(A or B or Cin)
            !$isunknown({A,B,Cin}) |-> ##0
            (S == (A ^ B ^ Cin))
          );

  a_cout: assert property (@(A or B or Cin)
            !$isunknown({A,B,Cin}) |-> ##0
            (Cout == ((A & B) | (Cin & (A ^ B))))
          );

  // Outputs must be known when inputs are known
  a_no_x: assert property (@(A or B or Cin)
            !$isunknown({A,B,Cin}) |-> ##0
            !$isunknown({S,Cout})
          );

  // Full functional coverage: all input combinations with expected outputs
  c_000: cover property (@(A or B or Cin) ({A,B,Cin}==3'b000) ##0 ({Cout,S}==2'b00));
  c_001: cover property (@(A or B or Cin) ({A,B,Cin}==3'b001) ##0 ({Cout,S}==2'b01));
  c_010: cover property (@(A or B or Cin) ({A,B,Cin}==3'b010) ##0 ({Cout,S}==2'b01));
  c_011: cover property (@(A or B or Cin) ({A,B,Cin}==3'b011) ##0 ({Cout,S}==2'b10));
  c_100: cover property (@(A or B or Cin) ({A,B,Cin}==3'b100) ##0 ({Cout,S}==2'b01));
  c_101: cover property (@(A or B or Cin) ({A,B,Cin}==3'b101) ##0 ({Cout,S}==2'b10));
  c_110: cover property (@(A or B or Cin) ({A,B,Cin}==3'b110) ##0 ({Cout,S}==2'b10));
  c_111: cover property (@(A or B or Cin) ({A,B,Cin}==3'b111) ##0 ({Cout,S}==2'b11));

  // Output value coverage
  co_00: cover property (@(A or B or Cin) ({Cout,S}==2'b00));
  co_01: cover property (@(A or B or Cin) ({Cout,S}==2'b01));
  co_10: cover property (@(A or B or Cin) ({Cout,S}==2'b10));
  co_11: cover property (@(A or B or Cin) ({Cout,S}==2'b11));

endmodule

// Bind to DUT
bind full_adder full_adder_sva u_full_adder_sva(.A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout));