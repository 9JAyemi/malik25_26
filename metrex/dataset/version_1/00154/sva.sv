// SVA checkers (bindable) for full_adder_2bit design

// Checker for top-level 2-bit adder
module full_adder_2bit_sva(
  input logic [1:0] A, B,
  input logic       Cin,
  input logic [1:0] S,
  input logic       Cout
);
  event comb_ev;  // sample on any combinational activity
  always @* -> comb_ev;
  default clocking cb @ (comb_ev); endclocking

  // Allow 0-delay settle on each sample
  assert property (1 |-> ##0 (S[0] == (A[0] ^ B[0])));
  assert property (1 |-> ##0 (S[1] == (A[1] ^ B[1])));
  assert property (1 |-> ##0 (Cout == ((A[0]&B[0]) | (A[1]&B[1]) | Cin)));

  // Stability: if inputs stable, outputs must be stable
  assert property ($stable({A,B,Cin}) |-> ##0 $stable({S,Cout}));

  // S must not depend on Cin when A,B are held
  assert property ($changed(Cin) && $stable({A,B}) |-> ##0 $stable(S));

  // No X/Z on outputs when inputs are clean
  assert property (!$isunknown({A,B,Cin}) |-> ##0 !$isunknown({S,Cout}));

  // Coverage (concise, hits key scenarios)
  cover property (1 |-> ##0 (!A[0] && !B[0] && !A[1] && !B[1] && !Cin && !Cout)); // no-carry case
  cover property (1 |-> ##0 ( A[0] &&  B[0] && !A[1] && !B[1] && !Cin &&  Cout)); // low-bit carry only
  cover property (1 |-> ##0 (!A[0] && !B[0] &&  A[1] &&  B[1] && !Cin &&  Cout)); // high-bit carry only
  cover property (1 |-> ##0 (!A[0] && !B[0] && !A[1] && !B[1] &&  Cin &&  Cout)); // Cin-only carry
  cover property (1 |-> ##0 ( A[0] &&  B[0] &&  A[1] &&  B[1] &&  Cin &&  Cout)); // all carry sources
  cover property ($changed(Cin) && $stable({A,B}));                               // Cin toggle w/ A,B held
  cover property ($changed(S[0]));
  cover property ($changed(S[1]));
endmodule

// Checker for half-adder cell
module HAHD2X_sva(
  input  logic A, B,
  input  logic CO, S
);
  event comb_ev; always @* -> comb_ev;
  default clocking cb @ (comb_ev); endclocking

  assert property (1 |-> ##0 (S  == (A ^ B)));
  assert property (1 |-> ##0 (CO == (A & B)));
  assert property (!$isunknown({A,B}) |-> ##0 !$isunknown({S,CO}));

  cover property ({A,B}==2'b00);
  cover property ({A,B}==2'b01);
  cover property ({A,B}==2'b10);
  cover property ({A,B}==2'b11);
endmodule

// Checker for or_gate helper
module or_gate_sva(
  input logic A, B, C,
  input logic Y
);
  event comb_ev; always @* -> comb_ev;
  default clocking cb @ (comb_ev); endclocking

  assert property (1 |-> ##0 (Y == (A | B | C)));
  assert property (!$isunknown({A,B,C}) |-> ##0 !$isunknown(Y));

  cover property (A||B||C);
  cover property (!A && !B && !C && !Y);
endmodule

// Bind checkers to DUTs
bind full_adder_2bit full_adder_2bit_sva i_full_adder_2bit_sva(.A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout));
bind HAHD2X          HAHD2X_sva          i_HAHD2X_sva         (.A(A), .B(B), .CO(CO), .S(S));
bind or_gate         or_gate_sva         i_or_gate_sva        (.A(A), .B(B), .C(C), .Y(Y));