// SVA for ripple_carry_adder and full_adder
// Bind-only; no DUT changes required

// Checker for top-level ripple-carry adder
module ripple_carry_adder_sva (
  input [3:0] A,
  input [3:0] B,
  input [3:0] R,
  input       Cout
);
  // Functional correctness (guard Xs, allow delta-cycle settle)
  assert property (@(A or B or R or Cout)
                   (!$isunknown({A,B})) |=> ##0 ({Cout,R} == ({1'b0,A} + {1'b0,B})))
    else $error("RCA: {Cout,R} != A+B");

  // No X/Z on outputs when inputs are clean
  assert property (@(A or B or R or Cout)
                   (!$isunknown({A,B})) |=> ##0 (!$isunknown({R,Cout}))))
    else $error("RCA: X/Z on outputs with known inputs");

  // Coverage: no-carry near-boundary
  cover property (@(A or B) (!$isunknown({A,B})) ##0
                  (A==4'h7 && B==4'h7 && R==4'hE && Cout==1'b0));

  // Coverage: carry-out occurs
  cover property (@(A or B) (!$isunknown({A,B})) ##0
                  (A + B >= 16 && Cout==1'b1));

  // Coverage: full ripple through all stages (F + 1 -> 0 with Cout)
  cover property (@(A or B) (!$isunknown({A,B})) ##0
                  (A==4'hF && B==4'h1 && R==4'h0 && Cout==1'b1));

  // Coverage: zero + zero
  cover property (@(A or B) (!$isunknown({A,B})) ##0
                  (A==4'h0 && B==4'h0 && R==4'h0 && Cout==1'b0));

  // Coverage: max + max
  cover property (@(A or B) (!$isunknown({A,B})) ##0
                  (A==4'hF && B==4'hF && R==4'hE && Cout==1'b1));
endmodule

// Checker for 1-bit full adder
module full_adder_sva (
  input A,
  input B,
  input Cin,
  input S,
  input Cout
);
  // Bit-accurate equations (guard Xs, allow delta-cycle settle)
  assert property (@(A or B or Cin or S or Cout)
                   (!$isunknown({A,B,Cin})) |=> ##0 (S == (A ^ B ^ Cin)))
    else $error("FA: S != A^B^Cin");

  assert property (@(A or B or Cin or S or Cout)
                   (!$isunknown({A,B,Cin})) |=> ##0 (Cout == ((A & B) | (Cin & (A ^ B)))))
    else $error("FA: Cout != (A&B)|(Cin&(A^B))");

  // Sum as arithmetic, with proper width
  assert property (@(A or B or Cin or S or Cout)
                   (!$isunknown({A,B,Cin})) |=> ##0 ({Cout,S} == ({1'b0,A}+{1'b0,B}+{1'b0,Cin})))
    else $error("FA: {Cout,S} != A+B+Cin");

  // No X/Z on outputs when inputs are clean
  assert property (@(A or B or Cin or S or Cout)
                   (!$isunknown({A,B,Cin})) |=> ##0 (!$isunknown({S,Cout}))))
    else $error("FA: X/Z on outputs with known inputs");

  // Coverage: generate, propagate, kill cases
  // Generate (A&B=1), both Cin polarities
  cover property (@(A or B or Cin) (! $isunknown({A,B,Cin})) ##0 (A & B) && (Cin==1'b0) && (Cout==1'b1) && (S==1'b0));
  cover property (@(A or B or Cin) (! $isunknown({A,B,Cin})) ##0 (A & B) && (Cin==1'b1) && (Cout==1'b1) && (S==1'b1));

  // Propagate (A^B=1), both Cin polarities
  cover property (@(A or B or Cin) (! $isunknown({A,B,Cin})) ##0 (A ^ B) && (Cin==1'b0) && (Cout==1'b0) && (S==1'b1));
  cover property (@(A or B or Cin) (! $isunknown({A,B,Cin})) ##0 (A ^ B) && (Cin==1'b1) && (Cout==1'b1) && (S==1'b0));

  // Kill (A==0,B==0), both Cin polarities
  cover property (@(A or B or Cin) (! $isunknown({A,B,Cin})) ##0 (~A & ~B) && (Cin==1'b0) && (Cout==1'b0) && (S==1'b0));
  cover property (@(A or B or Cin) (! $isunknown({A,B,Cin})) ##0 (~A & ~B) && (Cin==1'b1) && (Cout==1'b0) && (S==1'b1));
endmodule

// Bind checkers to DUTs
bind ripple_carry_adder ripple_carry_adder_sva u_rca_sva (.*);
bind full_adder        full_adder_sva        u_fa_sva   (.*);