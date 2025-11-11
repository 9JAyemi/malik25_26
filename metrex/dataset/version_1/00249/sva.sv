// SVA for ripple_adder and full_adder (concise, high-quality, bind-ready)
// Combinational sampling: trigger on any change and sample after ##0

// Full-adder SVA
module full_adder_sva
(
  input A,
  input B,
  input Cin,
  input S,
  input Cout
);
  event comb_ev; always @* -> comb_ev;

  // No X/Z on outputs when inputs are known
  assert property (@(comb_ev) !$isunknown({A,B,Cin}) |-> ##0 !$isunknown({S,Cout}));

  // Boolean equations and arithmetic consistency
  assert property (@(comb_ev) ##0 (S == (A ^ B ^ Cin)
                                && Cout == ((A & B) | (Cin & (A ^ B)))));
  assert property (@(comb_ev) ##0 ({Cout,S} == (A + B + Cin)));

  // Minimal functional coverage
  cover property (@(comb_ev) ##0 (A==0 && B==0 && Cin==0 && S==0 && Cout==0)); // kill
  cover property (@(comb_ev) ##0 (A==1 && B==1 && Cin==1 && Cout==1));         // generate/overflow
  cover property (@(comb_ev) ##0 ((A^B)==1 && Cin==1 && S==0 && Cout==1));     // propagate
endmodule

bind full_adder full_adder_sva fa_sva_i (.A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout));


// Ripple-adder SVA
module ripple_adder_sva #(parameter DW = 4)
(
  input  [DW-1:0] A,
  input  [DW-1:0] B,
  input           Cin,
  input  [DW-1:0] S,
  input           Cout
);
  // Note: internal carry[] is referenced directly via bind scope
  event comb_ev; always @* -> comb_ev;

  // No X/Z on outputs when inputs are known
  assert property (@(comb_ev) !$isunknown({A,B,Cin}) |-> ##0 !$isunknown({S,Cout}));

  // Endpoint and arithmetic correctness
  assert property (@(comb_ev) ##0 (carry[0] == Cin && Cout == carry[DW]));
  assert property (@(comb_ev) ##0 ({Cout,S} == (A + B + Cin)));

  // Bitwise correctness of sum and carry chain
  genvar i;
  generate
    for (i=0; i<DW; i++) begin : g_bit
      assert property (@(comb_ev)
                       !$isunknown({A,B,Cin}) |-> ##0
                       ( S[i] == (A[i] ^ B[i] ^ carry[i])
                      && carry[i+1] == ((A[i] & B[i]) | (carry[i] & (A[i] ^ B[i])))));
    end
  endgenerate

  // Targeted coverage
  // 1) Zero + Zero + 0 => Zero
  cover property (@(comb_ev) ##0 (A=={DW{1'b0}} && B=={DW{1'b0}} && Cin==0
                                  && S=={DW{1'b0}} && Cout==0));
  // 2) Max + Max + 1 => Overflow
  cover property (@(comb_ev) ##0 (A=={DW{1'b1}} && B=={DW{1'b1}} && Cin==1 && Cout==1));
  // 3) Full-width propagate chain (A^B all 1s, Cin=1) => all S=0, Cout=1
  cover property (@(comb_ev) ##0 ((A^B)=={DW{1'b1}} && Cin==1
                                  && S=={DW{1'b0}} && Cout==1));
  // 4) Observe both Cout states
  cover property (@(comb_ev) ##0 (Cout==0));
  cover property (@(comb_ev) ##0 (Cout==1));
endmodule

bind ripple_adder ripple_adder_sva #(.DW(DW))
  ra_sva_i (.A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout));