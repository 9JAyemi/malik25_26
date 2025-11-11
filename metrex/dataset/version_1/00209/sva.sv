// SVA for binary_adder: concise, strong functional checks + targeted coverage
bind binary_adder binary_adder_sva u_binary_adder_sva(.*);

module binary_adder_sva(
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       CIN,
  input  logic [3:0] S,
  input  logic       COUT
);

  // Functional correctness (golden check)
  assert property (@(A or B or CIN) {COUT,S} == (A + B + CIN))
    else $error("Adder mismatch: A=%0h B=%0h CIN=%0b -> S=%0h COUT=%0b", A,B,CIN,S,COUT);

  // X/Z propagation sanity: known inputs imply known outputs
  assert property (@(A or B or CIN) !$isunknown({A,B,CIN}) |-> !$isunknown({S,COUT}))
    else $error("Unknown on outputs with known inputs");

  // Helper: carry into MSB (bit 3)
  function automatic bit cin_msb();
    cin_msb = ((A[2:0] + B[2:0] + CIN) >= 8);
  endfunction

  // Corner-case coverage
  // Zero
  cover property (@(A or B or CIN) (A==4'h0 && B==4'h0 && CIN==1'b0 && S==4'h0 && COUT==1'b0));
  // Max overflow (31)
  cover property (@(A or B or CIN) (A==4'hF && B==4'hF && CIN==1'b1 && S==4'hF && COUT==1'b1));
  // Full propagate chain (A^B==all 1s, CIN=1 -> 16)
  cover property (@(A or B or CIN) ((A^B)==4'hF && CIN==1'b1 && S==4'h0 && COUT==1'b1));

  // MSB carry classes (kill/propagate/generate with/without carry-in)
  // No carry-in, MSB generate -> COUT=1
  cover property (@(A or B or CIN) (!cin_msb() && (A[3]&B[3]) && COUT==1));
  // Carry-in, MSB kill -> COUT=0
  cover property (@(A or B or CIN) ( cin_msb() && !(A[3]|B[3]) && COUT==0));
  // Carry-in, MSB propagate -> COUT=1
  cover property (@(A or B or CIN) ( cin_msb() && (A[3]^B[3]) && COUT==1));
  // No carry-in, MSB kill -> COUT=0
  cover property (@(A or B or CIN) (!cin_msb() && !(A[3]|B[3]) && COUT==0));

endmodule