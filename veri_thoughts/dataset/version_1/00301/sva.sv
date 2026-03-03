// SVA for full_adder (concise, high-quality, full functional checks + coverage)
// Bind these assertions to the DUT.

module full_adder_sva (input logic A, B, Cin, S, Cout);

  // Functional correctness (give outputs a delta to settle after any input change)
  assert property (@(A or B or Cin) !$isunknown({A,B,Cin}) |=> {Cout,S} == (A + B + Cin))
    else $error("full_adder: {Cout,S} != A+B+Cin");

  // Independent parity/majority checks (orthogonal to the adder check)
  assert property (@(A or B or Cin) !$isunknown({A,B,Cin}) |=> S == (A ^ B ^ Cin))
    else $error("full_adder: S != A^B^Cin");

  assert property (@(A or B or Cin) !$isunknown({A,B,Cin}) |=> Cout == ((A & B) | (B & Cin) | (A & Cin)))
    else $error("full_adder: Cout != majority(A,B,Cin)");

  // X/Z robustness
  assert property (@(A or B or Cin) !$isunknown({A,B,Cin}) |=> !$isunknown({S,Cout}))
    else $error("full_adder: X/Z on outputs with clean inputs");

  assert property (@(S or Cout) $isunknown({S,Cout}) |-> $isunknown({A,B,Cin}))
    else $error("full_adder: Spurious X/Z on outputs without X/Z on inputs");

  // Full input/output combination coverage (all 8 cases)
  cover property (@(A or B or Cin) !$isunknown({A,B,Cin}) |=> {A,B,Cin,S,Cout} == 5'b00000);
  cover property (@(A or B or Cin) !$isunknown({A,B,Cin}) |=> {A,B,Cin,S,Cout} == 5'b00101);
  cover property (@(A or B or Cin) !$isunknown({A,B,Cin}) |=> {A,B,Cin,S,Cout} == 5'b01001);
  cover property (@(A or B or Cin) !$isunknown({A,B,Cin}) |=> {A,B,Cin,S,Cout} == 5'b01110);
  cover property (@(A or B or Cin) !$isunknown({A,B,Cin}) |=> {A,B,Cin,S,Cout} == 5'b10001);
  cover property (@(A or B or Cin) !$isunknown({A,B,Cin}) |=> {A,B,Cin,S,Cout} == 5'b10110);
  cover property (@(A or B or Cin) !$isunknown({A,B,Cin}) |=> {A,B,Cin,S,Cout} == 5'b11010);
  cover property (@(A or B or Cin) !$isunknown({A,B,Cin}) |=> {A,B,Cin,S,Cout} == 5'b11111);

endmodule

// Bind to the DUT
bind full_adder full_adder_sva sva(.A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout));