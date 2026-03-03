// SVA checkers and binds for the adders

// One-bit full adder checker (purely combinational)
module one_bit_adder_sva (
  input A, B, CI,
  input SUM, COUT
);
  // Functional correctness: 2-bit result equals A+B+CI
  assert property (@(posedge A or negedge A or
                     posedge B or negedge B or
                     posedge CI or negedge CI)
                   {COUT,SUM} == (A + B + CI))
    else $error("one_bit_adder: {COUT,SUM} != A+B+CI");

  // Outputs never X/Z when inputs are 0/1
  assert property (@(posedge A or negedge A or
                     posedge B or negedge B or
                     posedge CI or negedge CI)
                   (!$isunknown({A,B,CI})) |-> (!$isunknown({SUM,COUT})))
    else $error("one_bit_adder: X/Z on outputs with known inputs");

  // Full input-space coverage (8 combinations)
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge CI or negedge CI)
                  {A,B,CI} == 3'b000);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge CI or negedge CI)
                  {A,B,CI} == 3'b001);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge CI or negedge CI)
                  {A,B,CI} == 3'b010);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge CI or negedge CI)
                  {A,B,CI} == 3'b011);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge CI or negedge CI)
                  {A,B,CI} == 3'b100);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge CI or negedge CI)
                  {A,B,CI} == 3'b101);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge CI or negedge CI)
                  {A,B,CI} == 3'b110);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge CI or negedge CI)
                  {A,B,CI} == 3'b111);
endmodule


// Full-adder wrapper checker (should still behave as a 1-bit full adder)
module full_adder_sva (
  input A, B, CI,
  input SUM, COUT
);
  // Golden functional check (this will flag the bug in SUM if CI=1)
  assert property (@(posedge A or negedge A or
                     posedge B or negedge B or
                     posedge CI or negedge CI)
                   {COUT,SUM} == (A + B + CI))
    else $error("full_adder: {COUT,SUM} != A+B+CI");

  // Outputs never X/Z when inputs are 0/1
  assert property (@(posedge A or negedge A or
                     posedge B or negedge B or
                     posedge CI or negedge CI)
                   (!$isunknown({A,B,CI})) |-> (!$isunknown({SUM,COUT})))
    else $error("full_adder: X/Z on outputs with known inputs");

  // Key functional scenarios covered
  // propagate: A^B=1, CI=1 -> SUM should toggle vs CI=0
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge CI or negedge CI)
                  (CI && (A^B)));
  // generate: A&B=1, CI=0 -> carry generated
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge CI or negedge CI)
                  (!CI && (A&B)));
endmodule


// Four-bit ripple-carry adder checker
module four_bit_adder_sva (
  input [3:0] A, B,
  input       CI,
  input [3:0] SUM,
  input       COUT,
  input       C1, C2, C3 // internal carries
);
  // Overall correctness against 5-bit golden sum
  assert property (@(posedge A[0] or negedge A[0] or
                     posedge A[1] or negedge A[1] or
                     posedge A[2] or negedge A[2] or
                     posedge A[3] or negedge A[3] or
                     posedge B[0] or negedge B[0] or
                     posedge B[1] or negedge B[1] or
                     posedge B[2] or negedge B[2] or
                     posedge B[3] or negedge B[3] or
                     posedge CI   or negedge CI)
                   {COUT,SUM} == ({1'b0,A} + {1'b0,B} + CI))
    else $error("four_bit_adder: {COUT,SUM} != A+B+CI");

  // Internal carry chain correctness
  assert property (@(posedge A[0] or negedge A[0] or posedge B[0] or negedge B[0] or posedge CI or negedge CI)
                   C1 == ((A[0]&B[0]) | (A[0]&CI) | (B[0]&CI)))
    else $error("four_bit_adder: C1 incorrect");
  assert property (@(posedge A[1] or negedge A[1] or posedge B[1] or negedge B[1] or posedge C1 or negedge C1)
                   C2 == ((A[1]&B[1]) | (A[1]&C1) | (B[1]&C1)))
    else $error("four_bit_adder: C2 incorrect");
  assert property (@(posedge A[2] or negedge A[2] or posedge B[2] or negedge B[2] or posedge C2 or negedge C2)
                   C3 == ((A[2]&B[2]) | (A[2]&C2) | (B[2]&C2)))
    else $error("four_bit_adder: C3 incorrect");

  // Per-bit sum correctness with local carries (pinpoints faulty stages)
  assert property (@(posedge A[0] or negedge A[0] or posedge B[0] or negedge B[0] or posedge CI or negedge CI)
                   SUM[0] == (A[0]^B[0]^CI))
    else $error("four_bit_adder: SUM[0] incorrect");
  assert property (@(posedge A[1] or negedge A[1] or posedge B[1] or negedge B[1] or posedge C1 or negedge C1)
                   SUM[1] == (A[1]^B[1]^C1))
    else $error("four_bit_adder: SUM[1] incorrect");
  assert property (@(posedge A[2] or negedge A[2] or posedge B[2] or negedge B[2] or posedge C2 or negedge C2)
                   SUM[2] == (A[2]^B[2]^C2))
    else $error("four_bit_adder: SUM[2] incorrect");
  assert property (@(posedge A[3] or negedge A[3] or posedge B[3] or negedge B[3] or posedge C3 or negedge C3)
                   SUM[3] == (A[3]^B[3]^C3))
    else $error("four_bit_adder: SUM[3] incorrect");

  // Outputs never X/Z when inputs are 0/1
  assert property (@(posedge A[0] or negedge A[0] or
                     posedge A[1] or negedge A[1] or
                     posedge A[2] or negedge A[2] or
                     posedge A[3] or negedge A[3] or
                     posedge B[0] or negedge B[0] or
                     posedge B[1] or negedge B[1] or
                     posedge B[2] or negedge B[2] or
                     posedge B[3] or negedge B[3] or
                     posedge CI   or negedge CI)
                   (!$isunknown({A,B,CI})) |-> (!$isunknown({SUM,COUT})))
    else $error("four_bit_adder: X/Z on outputs with known inputs");

  // Key coverage scenarios
  // Full ripple propagate across all 4 stages
  cover property (@(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or
                    posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
                    posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or
                    posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
                    posedge CI   or negedge CI)
                   ((A^B)==4'hF && CI));
  // No-carry case
  cover property (@(posedge A[0] or negedge A[0] or posedge B[0] or negedge B[0] or posedge CI or negedge CI)
                   (A==4'h0 && B==4'h0 && CI==1'b0));
  // Carry-generate at MSB
  cover property (@(posedge A[3] or negedge A[3] or posedge B[3] or negedge B[3] or posedge C3 or negedge C3)
                   (A[3]&B[3] && !C3));
endmodule


// Bind the checkers to the DUTs
bind one_bit_adder  one_bit_adder_sva  (.A(A), .B(B), .CI(CI), .SUM(SUM), .COUT(COUT));
bind full_adder     full_adder_sva     (.A(A), .B(B), .CI(CI), .SUM(SUM), .COUT(COUT));
bind four_bit_adder four_bit_adder_sva (.A(A), .B(B), .CI(CI), .SUM(SUM), .COUT(COUT),
                                        .C1(C1), .C2(C2), .C3(C3));