// SVA bind file for sky130_fd_sc_hd__fahcon
bind sky130_fd_sc_hd__fahcon fahcon_sva i_fahcon_sva (.*);

module fahcon_sva (
  input logic A,
  input logic B,
  input logic CI,
  input logic SUM,
  input logic COUT_N
);

  // No X/Z on outputs when inputs are known
  assert property (@(*) !$isunknown({A,B,CI}) |-> !$isunknown({SUM,COUT_N}))
    else $error("fahcon: X/Z on outputs with known inputs A=%b B=%b CI=%b SUM=%b COUT_N=%b", A,B,CI,SUM,COUT_N);

  // Arithmetic correctness: {Cout,Sum} == A+B+CI  (Cout = ~COUT_N)
  assert property (@(*) !$isunknown({A,B,CI}) |-> {~COUT_N, SUM} == ({1'b0,A}+{1'b0,B}+{1'b0,CI}))
    else $error("fahcon: arithmetic mismatch A=%b B=%b CI=%b SUM=%b COUT_N=%b", A,B,CI,SUM,COUT_N);

  // Parity (SUM) check
  assert property (@(*) !$isunknown({A,B,CI}) |-> SUM == (A ^ B ^ CI))
    else $error("fahcon: SUM parity mismatch A=%b B=%b CI=%b SUM=%b", A,B,CI,SUM);

  // Majority complement (COUT_N) check
  assert property (@(*) !$isunknown({A,B,CI}) |-> COUT_N == ~((A&B) | (A&CI) | (B&CI)))
    else $error("fahcon: COUT_N majority mismatch A=%b B=%b CI=%b COUT_N=%b", A,B,CI,COUT_N);

  // Input-space coverage (all 8 combinations)
  cover property (@(*) {A,B,CI} == 3'b000);
  cover property (@(*) {A,B,CI} == 3'b001);
  cover property (@(*) {A,B,CI} == 3'b010);
  cover property (@(*) {A,B,CI} == 3'b011);
  cover property (@(*) {A,B,CI} == 3'b100);
  cover property (@(*) {A,B,CI} == 3'b101);
  cover property (@(*) {A,B,CI} == 3'b110);
  cover property (@(*) {A,B,CI} == 3'b111);

  // Output-space coverage ({Cout,Sum} should realize all 4 values)
  cover property (@(*) {~COUT_N,SUM} == 2'b00);
  cover property (@(*) {~COUT_N,SUM} == 2'b01);
  cover property (@(*) {~COUT_N,SUM} == 2'b10);
  cover property (@(*) {~COUT_N,SUM} == 2'b11);

endmodule