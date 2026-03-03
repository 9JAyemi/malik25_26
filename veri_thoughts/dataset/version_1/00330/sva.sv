// SVA for full_adder and mux2. Bind these to the DUTs.
// Focused, high-signal-quality checks with concise full functional coverage.

module full_adder_sva (
  input logic A, B, Cin,
  input logic Sum, Cout
);
  // Functional correctness under known inputs
  assert property (@(A or B or Cin or Sum or Cout)
                   !$isunknown({A,B,Cin}) |-> ({Cout,Sum} == (A + B + Cin)));

  // Outputs must be known when inputs are known
  assert property (@(A or B or Cin) !$isunknown({A,B,Cin}) |-> !$isunknown({Sum,Cout}));

  // Full input-space coverage (8 combinations)
  cover property (@(A or B or Cin) {A,B,Cin} == 3'b000);
  cover property (@(A or B or Cin) {A,B,Cin} == 3'b001);
  cover property (@(A or B or Cin) {A,B,Cin} == 3'b010);
  cover property (@(A or B or Cin) {A,B,Cin} == 3'b011);
  cover property (@(A or B or Cin) {A,B,Cin} == 3'b100);
  cover property (@(A or B or Cin) {A,B,Cin} == 3'b101);
  cover property (@(A or B or Cin) {A,B,Cin} == 3'b110);
  cover property (@(A or B or Cin) {A,B,Cin} == 3'b111);

  // Output pattern coverage
  cover property (@(A or B or Cin) (Sum==0 && Cout==0));
  cover property (@(A or B or Cin) (Sum==1 && Cout==0));
  cover property (@(A or B or Cin) (Sum==0 && Cout==1));
  cover property (@(A or B or Cin) (Sum==1 && Cout==1));
endmodule

bind full_adder full_adder_sva u_full_adder_sva (
  .A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout)
);


// ----------------------------------------------------------------------------

module mux2_sva (
  input logic I0, I1, S,
  input logic O
);
  // Functional correctness under known inputs
  assert property (@(I0 or I1 or S or O)
                   !$isunknown({I0,I1,S}) |-> (O == (S ? I1 : I0)));

  // Output must be known when select and selected input are known
  assert property (@(I0 or I1 or S)
                   (!$isunknown(S) && (S ? !$isunknown(I1) : !$isunknown(I0)))
                   |-> !$isunknown(O));

  // Path coverage: both legs selected with both values
  cover property (@(I0 or I1 or S) (!S && I0==0 && O==0));
  cover property (@(I0 or I1 or S) (!S && I0==1 && O==1));
  cover property (@(I0 or I1 or S) ( S && I1==0 && O==0));
  cover property (@(I0 or I1 or S) ( S && I1==1 && O==1));

  // Select toggling coverage
  cover property (@(posedge S) 1);
  cover property (@(negedge S) 1);
endmodule

bind mux2 mux2_sva u_mux2_sva (
  .I0(I0), .I1(I1), .S(S), .O(O)
);