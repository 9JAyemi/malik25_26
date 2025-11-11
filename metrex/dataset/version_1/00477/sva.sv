// SVA checkers for add_sub and full_adder
// Bind into DUT; no TB changes needed.

module add_sub_sva;
  // Bound into add_sub scope: can see A,B,S,R,Cout,C
  default clocking cb @(*); endclocking

  // Helper 5-bit arithmetic
  logic [4:0] add_res, sub_res;
  always_comb begin
    add_res = {1'b0,A} + {1'b0,B};
    sub_res = {1'b0,A} + {1'b0,~B} + 5'd1; // A - B
  end

  // Sanity: no X/Z on inputs; outputs must be known if inputs are known
  assert property (!$isunknown({A,B,S})) else $error("add_sub: X/Z on inputs");
  assert property (!$isunknown({A,B,S}) |-> ##0 !$isunknown({R,Cout,C})) else $error("add_sub: X/Z on outputs/internal");

  // Functional spec
  assert property (S==1'b0 |-> ##0 {C[4],R} == add_res) else $error("add_sub: ADD mismatch");
  assert property (S==1'b1 |-> ##0 {C[4],R} == sub_res) else $error("add_sub: SUB mismatch");

  // Port carry must equal final ripple carry
  assert property (##0 Cout == C[4]) else $error("add_sub: Cout != final carry C[4]");

  // Ripple full-adder bitwise equations per stage
  genvar i;
  generate
    for (i=0;i<4;i++) begin : g_fa_eq
      assert property (##0 R[i] == (A[i]^B[i]^C[i])) else $error("add_sub: Sum bit %0d mismatch", i);
      assert property (##0 C[i+1] == ((A[i]&B[i]) | (C[i] & (A[i]^B[i])))) else $error("add_sub: Carry bit %0d mismatch", i+1);
    end
  endgenerate

  // Standard add/sub convention: initial carry-in equals S (useful to catch incorrect Cin handling)
  assert property (##0 C[0] == S) else $error("add_sub: C[0] != S (Cin convention)");

  // Coverage: exercise key scenarios
  cover property (S==0 && add_res[4]==0);             // add no carry
  cover property (S==0 && add_res[4]==1);             // add with carry
  cover property (S==1 && A>=B);                      // sub no borrow
  cover property (S==1 && A< B);                      // sub with borrow
  cover property (S==0 && A==4'hF && B==4'h1);        // add overflow corner
  cover property (S==1 && A==4'h0 && B==4'h1);        // sub underflow corner
  cover property (S==1 && A==B);                      // sub to zero
endmodule

bind add_sub add_sub_sva add_sub_sva_i();

module full_adder_sva;
  // Bound into full_adder: can see A,B,Cin,S,Cout
  default clocking cb @(*); endclocking
  assert property (##0 S == (A ^ B ^ Cin)) else $error("full_adder: Sum mismatch");
  assert property (##0 Cout == ((A & B) | (Cin & (A ^ B)))) else $error("full_adder: Carry mismatch");
  assert property (!$isunknown({A,B,Cin}) |-> ##0 !$isunknown({S,Cout})) else $error("full_adder: X/Z propagation");
  cover property (A==0 && B==0 && Cin==0);
  cover property (A==1 && B==1 && Cin==1);
endmodule

bind full_adder full_adder_sva full_adder_sva_i();