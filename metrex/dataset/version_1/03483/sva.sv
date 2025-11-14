// SVA for sky130_fd_sc_ms__fah
// Bind this module to the DUT to check combinational correctness and cover all cases.

module sky130_fd_sc_ms__fah_sva;

  // Trigger on any change to inputs/outputs to sample combinationally
  event comb_ev;
  always @(A or B or CI or SUM or COUT) -> comb_ev;

  // Functional correctness incl. internal wiring, when inputs are known
  property p_func;
    @(comb_ev) !$isunknown({A,B,CI}) |-> (
      {COUT,SUM} == A + B + CI &&
      xor0_out_SUM == (A ^ B ^ CI) &&
      a_b         == (A & B) &&
      a_ci        == (A & CI) &&
      b_ci        == (B & CI) &&
      or0_out_COUT == (a_b | a_ci | b_ci) &&
      SUM         == xor0_out_SUM &&
      COUT        == or0_out_COUT
    );
  endproperty
  assert property (p_func);

  // No X on any output/internal when inputs are known
  assert property (@(comb_ev)
    !$isunknown({A,B,CI}) |-> !$isunknown({SUM,COUT,xor0_out_SUM,a_b,a_ci,b_ci,or0_out_COUT})
  );

  // Full truth-table coverage (inputs and expected outputs)
  cover property (@(comb_ev) A==0 && B==0 && CI==0 && SUM==0 && COUT==0);
  cover property (@(comb_ev) A==0 && B==0 && CI==1 && SUM==1 && COUT==0);
  cover property (@(comb_ev) A==0 && B==1 && CI==0 && SUM==1 && COUT==0);
  cover property (@(comb_ev) A==0 && B==1 && CI==1 && SUM==0 && COUT==1);
  cover property (@(comb_ev) A==1 && B==0 && CI==0 && SUM==1 && COUT==0);
  cover property (@(comb_ev) A==1 && B==0 && CI==1 && SUM==0 && COUT==1);
  cover property (@(comb_ev) A==1 && B==1 && CI==0 && SUM==0 && COUT==1);
  cover property (@(comb_ev) A==1 && B==1 && CI==1 && SUM==1 && COUT==1);

endmodule

bind sky130_fd_sc_ms__fah sky130_fd_sc_ms__fah_sva svas();