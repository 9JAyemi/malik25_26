// SVA for ripple_carry_adder and half_adder
// Bindable, concise, and checks functionality, structure, connectivity, and key coverage

// Ripple-carry adder SVA (bind inside ripple_carry_adder)
module rca_sva(
  input  logic [3:0] A, B,
  input  logic       Cin,
  input  logic [3:0] Sum,
  input  logic       Cout,
  input  logic [3:0] s, c,                    // internal nets
  input  logic       ha0CIN, ha1CIN, ha2CIN, ha3CIN, ha3COUT // sub-inst port taps
);
  default clocking cb @(A or B or Cin or Sum or Cout or s or c
                        or ha0CIN or ha1CIN or ha2CIN or ha3CIN or ha3COUT); endclocking

  let carry(a,b,ci) = (a & b) | (a & ci) | (b & ci);
  let sum  (a,b,ci) =  a ^ b ^ ci;

  // Top-level functional correctness and X-propagation
  assert property (!$isunknown({A,B,Cin}) |-> {Cout,Sum} == A + B + Cin);
  assert property (!$isunknown({A,B,Cin}) |-> !$isunknown({Sum,Cout}));

  // Structural ripple equations (bitwise) and final carry
  assert property (!$isunknown({A[0],B[0],Cin}) |-> s[0] == sum  (A[0],B[0],Cin) && c[0] == carry(A[0],B[0],Cin));
  assert property (!$isunknown({A[1],B[1],c[0]}) |-> s[1] == sum  (A[1],B[1],c[0]) && c[1] == carry(A[1],B[1],c[0]));
  assert property (!$isunknown({A[2],B[2],c[1]}) |-> s[2] == sum  (A[2],B[2],c[1]) && c[2] == carry(A[2],B[2],c[1]));
  assert property (!$isunknown({A[3],B[3],c[2]}) |-> s[3] == sum  (A[3],B[3],c[2]) && Cout  == carry(A[3],B[3],c[2]));

  // Output wiring
  assert property (Sum == s);

  // Connectivity checks into sub-adders (flags missing/incorrect CIN wiring)
  assert property (ha0CIN === Cin);
  assert property (ha1CIN === c[0]);
  assert property (ha2CIN === c[1]);
  assert property (ha3CIN === c[2]);
  assert property (ha3COUT === Cout);

  // Key functional covers
  cover property (Cin && A==4'b0000 && B==4'b0000 && Sum==4'b0001 && Cout==1'b0);         // Cin affects LSB
  cover property ((A ^ B) == 4'hF && Cin && {Cout,Sum} == 5'b1_0000);                      // full propagate chain
  cover property ((A & B) != 4'b0000);                                                     // some generate
  cover property ((A ^ B) != 4'b0000);                                                     // some propagate
  cover property (~|(A | B));                                                              // all-zero kill
endmodule

// Full-adder cell SVA (bind inside half_adder)
module fa_sva(
  input logic A, B, CIN,
  input logic SUM, COUT
);
  default clocking cb @(A or B or CIN or SUM or COUT); endclocking
  let carry(a,b,ci) = (a & b) | (a & ci) | (b & ci);
  let sum  (a,b,ci) =  a ^ b ^ ci;

  assert property (!$isunknown({A,B,CIN}) |-> {COUT,SUM} == A + B + CIN);
  assert property (!$isunknown({A,B,CIN}) |-> SUM == sum(A,B,CIN) && COUT == carry(A,B,CIN));
  assert property (!$isunknown({A,B,CIN}) |-> !$isunknown({SUM,COUT}));

  cover property (CIN && (A ^ B)); // propagate case with Cin
  cover property ((A & B));        // generate case
endmodule

// Binds
bind ripple_carry_adder rca_sva rca_sva_i (
  .A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout),
  .s(s), .c(c),
  .ha0CIN(ha0.CIN), .ha1CIN(ha1.CIN), .ha2CIN(ha2.CIN), .ha3CIN(ha3.CIN), .ha3COUT(ha3.COUT)
);

bind half_adder fa_sva fa_sva_i (
  .A(A), .B(B), .CIN(CIN), .SUM(SUM), .COUT(COUT)
);