// SVA checker for Ripple_Carry_Adder
module RCA_SVA (
  input logic [3:0] A, B,
  input logic       Cin,
  input logic [3:0] S,
  input logic       Cout
);
  event comb_ev;
  always @* -> comb_ev;
  default clocking cb @(comb_ev); endclocking

  function automatic bit known_inputs();
    return !$isunknown({A,B,Cin});
  endfunction

  function automatic [4:0] add4(input logic [3:0] a,b, input logic cin);
    add4 = a + b + cin;
  endfunction

  function automatic bit cin_at(int idx);
    bit c = Cin;
    for (int k=0; k<idx; k++) begin
      c = (A[k] & B[k]) | (c & (A[k]^B[k]));
    end
    return c;
  endfunction

  function automatic bit carry_out_at(int idx);
    bit c = cin_at(idx);
    return (A[idx] & B[idx]) | (c & (A[idx]^B[idx]));
  endfunction

  // Functional correctness
  assert property (known_inputs() |-> {Cout,S} == add4(A,B,Cin));
  assert property (known_inputs() |-> !$isunknown({Cout,S}));

  // Per-bit sum checks
  genvar i;
  generate
    for (i=0;i<4;i++) begin : g_sum
      assert property (known_inputs() |-> S[i] == (A[i]^B[i]^cin_at(i)));
    end
  endgenerate

  // Carry behavior (generate/propagate/kill) and coverage for stages 0..2
  genvar j;
  generate
    for (j=0;j<3;j++) begin : g_carry
      assert property (known_inputs() && (A[j] & B[j]) |-> carry_out_at(j));          // generate
      assert property (known_inputs() && (A[j] ^ B[j]) && cin_at(j) |-> carry_out_at(j)); // propagate
      assert property (known_inputs() && (~A[j] & ~B[j]) && cin_at(j) |-> !carry_out_at(j)); // kill

      cover property (known_inputs() && (A[j] & B[j]) && carry_out_at(j));
      cover property (known_inputs() && (A[j] ^ B[j]) && cin_at(j) && carry_out_at(j));
      cover property (known_inputs() && (~A[j] & ~B[j]) && cin_at(j) && !carry_out_at(j));
    end
  endgenerate

  // MSB carry-out and key corner coverage
  assert property (known_inputs() |-> Cout == carry_out_at(3));
  cover property (known_inputs() && {Cout,S} == 5'd0);   // 0+0+0
  cover property (known_inputs() && {Cout,S} == 5'h10);  // overflow to 16
  cover property (known_inputs() && Cout && (S==4'hF));  // max overflow pattern
endmodule

bind Ripple_Carry_Adder RCA_SVA rca_sva_i(.A(A),.B(B),.Cin(Cin),.S(S),.Cout(Cout));


// SVA checker for Full_Adder (1-bit correctness, X safety, and basic coverage)
module FA_SVA (
  input logic A, B, Cin,
  input logic S, Cout
);
  event comb_ev;
  always @* -> comb_ev;
  default clocking cb @(comb_ev); endclocking

  function automatic bit known_inputs();
    return !$isunknown({A,B,Cin});
  endfunction

  assert property (known_inputs() |-> {Cout,S} == (A + B + Cin));
  assert property (known_inputs() |-> !$isunknown({Cout,S}));

  // Minimal but meaningful coverage of FA modes
  cover property (known_inputs() && {A,B,Cin}==3'b000);
  cover property (known_inputs() && {A,B,Cin}==3'b111);
  cover property (known_inputs() && (A&B) && Cout);            // generate
  cover property (known_inputs() && (A^B) && Cin && Cout);     // propagate
  cover property (known_inputs() && (~A & ~B) && Cin && !Cout);// kill
endmodule

bind Full_Adder FA_SVA fa_sva_i(.A(A),.B(B),.Cin(Cin),.S(S),.Cout(Cout));