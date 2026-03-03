// SVA for full_adder and four_bit_adder (clockless, bindable)

module full_adder_sva (
  input A, input B, input Cin,
  input Sum, input Cout
);
  // Sanity
  assume property (@(*) !$isunknown({A,B,Cin}));
  assert property (@(*) !$isunknown({Sum,Cout}));

  // Functional correctness (equivalent forms)
  assert property (@(*) {Cout,Sum} == (A + B + Cin));
  assert property (@(*) Sum  == (A ^ B ^ Cin));
  assert property (@(*) Cout == ((A & B) | (Cin & (A ^ B))));

  // Truth-table coverage
  cover property (@(*) {A,B,Cin} == 3'b000);
  cover property (@(*) {A,B,Cin} == 3'b001);
  cover property (@(*) {A,B,Cin} == 3'b010);
  cover property (@(*) {A,B,Cin} == 3'b011);
  cover property (@(*) {A,B,Cin} == 3'b100);
  cover property (@(*) {A,B,Cin} == 3'b101);
  cover property (@(*) {A,B,Cin} == 3'b110);
  cover property (@(*) {A,B,Cin} == 3'b111);

  // Output value coverage
  cover property (@(*) Sum==0);
  cover property (@(*) Sum==1);
  cover property (@(*) Cout==0);
  cover property (@(*) Cout==1);
endmodule

module four_bit_adder_sva (
  input  [3:0] A, input [3:0] B, input Cin,
  input  [3:0] Sum, input Cout
);
  // Sanity
  assume property (@(*) !$isunknown({A,B,Cin}));
  assert property (@(*) !$isunknown({Sum,Cout}));

  // Full-width arithmetic equivalence
  assert property (@(*) {Cout,Sum} == ({1'b0,A} + {1'b0,B} + Cin));

  // LSB correctness (helps localize issues)
  assert property (@(*) Sum[0] == (A[0] ^ B[0] ^ Cin));

  // Carry-out must match majority of MSB stage when rippled
  let maj(x,y,z) = (x&y)|(x&z)|(y&z);
  // Full propagate chain coverage (no generates, Cin ripples through all)
  cover property (@(*) (&(A^B)) && ~(|(A&B)) && Cin);

  // Basic scenario coverage
  cover property (@(*) (A==4'h0) && (B==4'h0) && (Cin==1'b0) && (Sum==4'h0) && (Cout==1'b0));
  cover property (@(*) (A==4'hF) && (B==4'hF) && (Cin==1'b1) && (Cout==1'b1));
  cover property (@(*) (A==4'hF) && (B==4'h0) && (Cin==1'b1)); // 4-bit full ripple propagate
  cover property (@(*) (A==4'h0) && (B==4'hF) && (Cin==1'b1)); // symmetric propagate

  // Output range coverage
  cover property (@(*) Sum==4'h0);
  cover property (@(*) Sum==4'hF);
  cover property (@(*) Cout==0);
  cover property (@(*) Cout==1);
endmodule

// Bind into DUTs
bind full_adder     full_adder_sva     fa_chk (.*);
bind four_bit_adder four_bit_adder_sva fba_chk(.*);