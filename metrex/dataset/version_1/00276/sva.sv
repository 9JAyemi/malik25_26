// SVA for RippleCarryAdder and FA

module rca_sva (input  logic [3:0] A, B, S,
                input  logic       Cin, Cout,
                input  logic [3:0] w1, w2);
  // Sample on any combinational change
  event comb_ev;
  always_comb -> comb_ev;

  // No X/Z on outputs when inputs are known
  assert property (@(comb_ev) !$isunknown({A,B,Cin}) |-> !$isunknown({S,Cout,w1,w2[2:0]}));

  // S matches internal sum bus
  assert property (@(comb_ev) S === w1);

  // End-to-end 4-bit add correctness
  assert property (@(comb_ev) disable iff ($isunknown({A,B,Cin}))
                   {Cout,S} == A + B + Cin);

  // Per-bit ripple chain correctness
  assert property (@(comb_ev) disable iff ($isunknown({A,B,Cin}))
                   {w2[0], w1[0]} == (A[0] + B[0] + Cin));
  assert property (@(comb_ev) disable iff ($isunknown({A,B,Cin}))
                   {w2[1], w1[1]} == (A[1] + B[1] + w2[0]));
  assert property (@(comb_ev) disable iff ($isunknown({A,B,Cin}))
                   {w2[2], w1[2]} == (A[2] + B[2] + w2[1]));
  assert property (@(comb_ev) disable iff ($isunknown({A,B,Cin}))
                   {Cout , w1[3]} == (A[3] + B[3] + w2[2]));

  // Functional coverage (key scenarios)
  cover property (@(comb_ev) A==4'h0 && B==4'h0 && Cin==1'b0);
  cover property (@(comb_ev) A==4'h0 && B==4'h0 && Cin==1'b1);
  cover property (@(comb_ev) (A^B)==4'hF && Cin==1'b1 && Cout==1'b1 && S==4'h0); // full propagate
  cover property (@(comb_ev) (A[3]&B[3]) && Cout==1'b1);                          // MSB generate
  cover property (@(comb_ev) A==4'hF && B==4'h1 && Cin==1'b0 && Cout==1'b1 && S==4'h0); // overflow
endmodule

module fa_sva (input logic A, B, Cin, S, Cout);
  event comb_ev;
  always_comb -> comb_ev;

  // No X/Z on outputs when inputs are known
  assert property (@(comb_ev) !$isunknown({A,B,Cin}) |-> !$isunknown({S,Cout}));

  // 1-bit full adder correctness
  assert property (@(comb_ev) disable iff ($isunknown({A,B,Cin}))
                   {Cout,S} == (A + B + Cin));

  // Cover all 8 input combinations
  cover property (@(comb_ev) !A && !B && !Cin);
  cover property (@(comb_ev) !A && !B &&  Cin);
  cover property (@(comb_ev) !A &&  B && !Cin);
  cover property (@(comb_ev) !A &&  B &&  Cin);
  cover property (@(comb_ev)  A && !B && !Cin);
  cover property (@(comb_ev)  A && !B &&  Cin);
  cover property (@(comb_ev)  A &&  B && !Cin);
  cover property (@(comb_ev)  A &&  B &&  Cin);
endmodule

// Bind into DUTs
bind RippleCarryAdder rca_sva rca_sva_i(.A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout), .w1(w1), .w2(w2));
bind FA              fa_sva  fa_sva_i (.A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout));