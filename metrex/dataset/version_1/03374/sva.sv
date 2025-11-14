// SVA checkers for RCA_N4_17 and its full adders.
// Bind these into your simulation; concise but thorough.

module rca4_sva (
  input  logic [3:0] A, B,
  input  logic       Ci,
  input  logic [3:0] S,
  input  logic       Co,
  input  logic [3:1] CTMP
);
  default clocking cb @(*); endclocking

  // Arithmetic correctness (allow 0-delay settle)
  assert property ( ##0 ({Co,S} == A + B + Ci) );

  // Bit-level sum and carry at each stage
  assert property ( ##0 (S[0]    == (A[0]^B[0]^Ci)) );
  assert property ( ##0 (CTMP[1] == ((A[0]&B[0]) | (A[0]&Ci)      | (B[0]&Ci))) );

  assert property ( ##0 (S[1]    == (A[1]^B[1]^CTMP[1])) );
  assert property ( ##0 (CTMP[2] == ((A[1]&B[1]) | (A[1]&CTMP[1]) | (B[1]&CTMP[1]))) );

  assert property ( ##0 (S[2]    == (A[2]^B[2]^CTMP[2])) );
  assert property ( ##0 (CTMP[3] == ((A[2]&B[2]) | (A[2]&CTMP[2]) | (B[2]&CTMP[2]))) );

  assert property ( ##0 (S[3]    == (A[3]^B[3]^CTMP[3])) );
  assert property ( ##0 (Co      == ((A[3]&B[3]) | (A[3]&CTMP[3]) | (B[3]&CTMP[3]))) );

  // Knownness: known inputs imply known outputs
  property known_outputs;
    !$isunknown({A,B,Ci}) |-> ##0 !$isunknown({S,Co,CTMP});
  endproperty
  assert property ( known_outputs );

  // Useful coverage
  cover property ( ##0 ((A^B)==4'hF && Ci && {Co,S}==5'h10) ); // full propagate chain
  cover property ( ##0 ((A&B)!=4'h0) );                        // any generate
  cover property ( ##0 (Co && !Ci) );                          // carry generated without initial carry
  cover property ( ##0 ({Co,S}==5'h00) );                      // zero result
  cover property ( ##0 ({Co,S}==5'h1F) );                      // max result (overflow)
endmodule

module fa_sva (
  input logic A,B,Ci,
  input logic S,Co
);
  default clocking cb @(*); endclocking

  assert property ( ##0 (S  == (A^B^Ci)) );
  assert property ( ##0 (Co == ((A&B)|(A&Ci)|(B&Ci))) );

  cover property ( ##0 (A^B) ); // propagate condition
  cover property ( ##0 (A&B) ); // generate condition
endmodule

// Bind checkers
bind RCA_N4_17 rca4_sva u_rca4_sva (.A(A), .B(B), .Ci(Ci), .S(S), .Co(Co), .CTMP(CTMP));
bind FA_68     fa_sva   u_fa68_sva  (.A(A), .B(B), .Ci(Ci), .S(S), .Co(Co));
bind FA_69     fa_sva   u_fa69_sva  (.A(A), .B(B), .Ci(Ci), .S(S), .Co(Co));
bind FA_70     fa_sva   u_fa70_sva  (.A(A), .B(B), .Ci(Ci), .S(S), .Co(Co));
bind FA_71     fa_sva   u_fa71_sva  (.A(A), .B(B), .Ci(Ci), .S(S), .Co(Co));