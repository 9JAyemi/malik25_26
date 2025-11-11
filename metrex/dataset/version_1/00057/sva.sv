// SVA for sky130_fd_sc_lp__fah (full adder)
// Concise, comprehensive functional checks + full truth-table coverage.
// Bind this module to the DUT.

module fah_sva (
  input logic A,
  input logic B,
  input logic CI,
  input logic SUM,
  input logic COUT
);

  // Helper
  wire inputs_known = !$isunknown({A,B,CI});

  // Outputs must be known when inputs are known
  ap_known: assert property (inputs_known |-> !$isunknown({SUM,COUT}));

  // Functional correctness (both outputs together and individually)
  ap_fulladd: assert property (inputs_known |-> {COUT, SUM} == (A + B + CI));
  ap_sum:     assert property (inputs_known |-> SUM  == (A ^ B ^ CI));
  ap_cout:    assert property (inputs_known |-> COUT == ((A & B) | (A & CI) | (B & CI)));

  // Truth-table coverage (all 8 input combinations with expected outputs)
  cp_000: cover property (A==0 && B==0 && CI==0 && SUM==0 && COUT==0);
  cp_001: cover property (A==0 && B==0 && CI==1 && SUM==1 && COUT==0);
  cp_010: cover property (A==0 && B==1 && CI==0 && SUM==1 && COUT==0);
  cp_011: cover property (A==0 && B==1 && CI==1 && SUM==0 && COUT==1);
  cp_100: cover property (A==1 && B==0 && CI==0 && SUM==1 && COUT==0);
  cp_101: cover property (A==1 && B==0 && CI==1 && SUM==0 && COUT==1);
  cp_110: cover property (A==1 && B==1 && CI==0 && SUM==0 && COUT==1);
  cp_111: cover property (A==1 && B==1 && CI==1 && SUM==1 && COUT==1);

endmodule

// Bind into the DUT
bind sky130_fd_sc_lp__fah fah_sva u_fah_sva (.A(A), .B(B), .CI(CI), .SUM(SUM), .COUT(COUT));