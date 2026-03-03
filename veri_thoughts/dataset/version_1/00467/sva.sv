// SVA for full_adder
module full_adder_sva(input A, input B, input CI, input S, input CO);
  default clocking cb @(posedge $global_clock); endclocking
  default disable iff ($isunknown({A,B,CI,S,CO}));

  // Functional correctness
  assert property ({CO,S} == (A + B + CI));
  assert property (S == (A ^ B ^ CI));
  assert property (CO == ((A & B) | (CI & (A ^ B))));

  // Full input space coverage (8 combos)
  cover property ({A,B,CI} == 3'b000);
  cover property ({A,B,CI} == 3'b001);
  cover property ({A,B,CI} == 3'b010);
  cover property ({A,B,CI} == 3'b011);
  cover property ({A,B,CI} == 3'b100);
  cover property ({A,B,CI} == 3'b101);
  cover property ({A,B,CI} == 3'b110);
  cover property ({A,B,CI} == 3'b111);

  // Output space coverage
  cover property ({CO,S} == 2'b00);
  cover property ({CO,S} == 2'b01);
  cover property ({CO,S} == 2'b10);
  cover property ({CO,S} == 2'b11);
endmodule

bind full_adder full_adder_sva fa_sva(.A(A), .B(B), .CI(CI), .S(S), .CO(CO));


// SVA for four_bit_adder
module four_bit_adder_sva(
  input  [3:0] A,
  input  [3:0] B,
  input  [3:0] S,
  input  [3:0] CO_int,   // note: CO_int[3] is unused in DUT; do not gate on it
  input  [4:0] C,
  input        CO
);
  default clocking cb @(posedge $global_clock); endclocking
  // Do not include CO_int[3] in unknown gating (it is undriven in DUT)
  default disable iff ($isunknown({A,B,S,CO_int[2:0],C,CO}));

  // Top-level arithmetic and output wiring
  assert property ({CO,S} == (A + B));
  assert property (C == {CO,S});

  // Bit 0: CI == 0 behavior enforced
  assert property (S[0] == (A[0] ^ B[0]));
  assert property (CO_int[0] == (A[0] & B[0]));

  // Ripple stages
  assert property ({CO_int[1], S[1]} == (A[1] + B[1] + CO_int[0]));
  assert property ({CO_int[2], S[2]} == (A[2] + B[2] + CO_int[1]));
  assert property ({CO,         S[3]} == (A[3] + B[3] + CO_int[2]));

  // Coverage: key scenarios
  cover property (A == 4'h0 && B == 4'h0 && CO == 1'b0 && S == 4'h0);     // 0+0
  cover property (A == 4'hF && B == 4'hF && CO == 1'b1 && S == 4'hE);     // max+max
  cover property (S == 4'h0 && CO == 1'b1);                                // sum == 16
  cover property (CO == 1'b1);                                             // overflow seen
  cover property (CO == 1'b0);                                             // no overflow seen
  cover property (CO_int[0]);                                              // carry out of bit0
  cover property (CO_int[1]);                                              // carry out of bit1
  cover property (CO_int[2]);                                              // carry out of bit2
  cover property (CO_int[0] && CO_int[1] && CO_int[2] && CO);              // long ripple
endmodule

bind four_bit_adder four_bit_adder_sva add4_sva(.A(A), .B(B), .S(S), .CO_int(CO_int), .C(C), .CO(CO));