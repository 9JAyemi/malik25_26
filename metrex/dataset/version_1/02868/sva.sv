// SVA checker for bin_adder
module bin_adder_sva (
  input logic A,
  input logic B,
  input logic CI,
  input logic SUM,
  input logic COUT_N
);
  // Sample on any relevant combinational change
  default clocking cb @ (A or B or CI or SUM or COUT_N); endclocking

  // Inputs known => outputs known
  assert property ( !$isunknown({A,B,CI}) |-> !$isunknown({SUM,COUT_N}) );

  // Functional correctness: 1-bit full-adder truth (2-bit sum)
  assert property ( !$isunknown({A,B,CI}) |-> {COUT_N,SUM} == A + B + CI );

  // Optional orthogonal form (majority carry) to catch logical mismatches
  assert property ( !$isunknown({A,B,CI}) |-> COUT_N == ((A & B) | (B & CI) | (A & CI)) );
  assert property ( !$isunknown({A,B,CI}) |-> SUM == (A ^ B ^ CI) );

  // Full truth-table coverage (inputs exercised and outputs match)
  cover property ( {A,B,CI}==3'b000 && {COUT_N,SUM}==2'b00 );
  cover property ( {A,B,CI}==3'b001 && {COUT_N,SUM}==2'b01 );
  cover property ( {A,B,CI}==3'b010 && {COUT_N,SUM}==2'b01 );
  cover property ( {A,B,CI}==3'b011 && {COUT_N,SUM}==2'b10 );
  cover property ( {A,B,CI}==3'b100 && {COUT_N,SUM}==2'b01 );
  cover property ( {A,B,CI}==3'b101 && {COUT_N,SUM}==2'b10 );
  cover property ( {A,B,CI}==3'b110 && {COUT_N,SUM}==2'b10 );
  cover property ( {A,B,CI}==3'b111 && {COUT_N,SUM}==2'b11 );
endmodule

// Bind the checker to the DUT
bind bin_adder bin_adder_sva u_bin_adder_sva (
  .A(A),
  .B(B),
  .CI(CI),
  .SUM(SUM),
  .COUT_N(COUT_N)
);