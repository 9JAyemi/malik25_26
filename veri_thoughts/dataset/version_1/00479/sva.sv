// SVA for sky130_fd_sc_lp__ha (half-adder)
// Bind into the DUT; checks functional correctness, X handling, and basic coverage.

module sky130_fd_sc_lp__ha_sva (
  input logic A,
  input logic B,
  input logic SUM,
  input logic COUT
);

  // Functional correctness when inputs are known; also ensures outputs are known
  a_function: assert property (@(*)
    !$isunknown({A,B}) |-> (!$isunknown({COUT,SUM}) &&
                            {COUT,SUM} == ({1'b0,A} + {1'b0,B}))
  );

  // Safety invariants (hold unconditionally)
  a_not_both1:        assert property (@(*) !(COUT && SUM));      // impossible sum=carry=1
  a_cout_means_ab11:  assert property (@(*) COUT |-> (A && B));    // carry implies A=B=1
  a_sum_parity:       assert property (@(*) !$isunknown({A,B}) |-> (SUM == (A ^ B)));

  // Functional coverage: all input/output combinations
  c_00: cover property (@(*) (!A && !B && !COUT && !SUM));
  c_01: cover property (@(*) ( A && !B && !COUT &&  SUM));
  c_10: cover property (@(*) (!A &&  B && !COUT &&  SUM));
  c_11: cover property (@(*) ( A &&  B &&  COUT && !SUM));

  // Toggle coverage on any input edge
  c_sum_rise:  cover property (@(posedge A or negedge A or posedge B or negedge B) $rose(SUM));
  c_sum_fall:  cover property (@(posedge A or negedge A or posedge B or negedge B) $fell(SUM));
  c_cout_rise: cover property (@(posedge A or negedge A or posedge B or negedge B) $rose(COUT));
  c_cout_fall: cover property (@(posedge A or negedge A or posedge B or negedge B) $fell(COUT));

endmodule

bind sky130_fd_sc_lp__ha sky130_fd_sc_lp__ha_sva ha_sva_i (.*);