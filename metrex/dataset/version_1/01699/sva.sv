// SVA checker for sky130_fd_sc_ms__ha (half-adder)
// Concise functional checks, X checks, and basic coverage.

`ifndef SKY130_FD_SC_MS__HA_SVA
`define SKY130_FD_SC_MS__HA_SVA

module sky130_fd_sc_ms__ha_sva (
  input logic A, B,
  input logic SUM, COUT
);

  // Sample on any input edge
  default clocking cb @(posedge A or negedge A or posedge B or negedge B); endclocking

  // Expected functions
  let exp_sum  = A ^ B;
  let exp_cout = A & B;

  // Functional correctness (after delta)
  property p_func;
    !$isunknown({A,B}) |-> ##0 (SUM == exp_sum && COUT == exp_cout);
  endproperty
  assert property (p_func) else $error("HA: SUM/COUT mismatch");

  // No X/Z on outputs when inputs known
  property p_no_x_out;
    !$isunknown({A,B}) |-> ##0 !$isunknown({SUM,COUT});
  endproperty
  assert property (p_no_x_out) else $error("HA: X/Z on outputs with known inputs");

  // Sanity: COUT high only when both inputs 1
  property p_cout_implies_both1;
    @(posedge COUT or negedge COUT or posedge A or negedge A or posedge B or negedge B)
      COUT |-> (A && B);
  endproperty
  assert property (p_cout_implies_both1) else $error("HA: COUT=1 but A&B!=1");

  // Sanity: with known inputs, SUM and COUT cannot both be 1
  property p_no_both1;
    !$isunknown({A,B}) |-> ##0 !(SUM && COUT);
  endproperty
  assert property (p_no_both1) else $error("HA: SUM and COUT both 1");

  // Outputs only change when an input changes (no spurious glitches)
  property p_out_change_needs_in_change;
    @(posedge SUM or negedge SUM or posedge COUT or negedge COUT)
      ($changed(A) || $changed(B));
  endproperty
  assert property (p_out_change_needs_in_change) else $error("HA: Output changed without input change");

  // Truth-table coverage (inputs known)
  cover property (!$isunknown({A,B}) && A==0 && B==0 && SUM==0 && COUT==0);
  cover property (!$isunknown({A,B}) && A==0 && B==1 && SUM==1 && COUT==0);
  cover property (!$isunknown({A,B}) && A==1 && B==0 && SUM==1 && COUT==0);
  cover property (!$isunknown({A,B}) && A==1 && B==1 && SUM==0 && COUT==1);

  // Toggle coverage
  cover property ($changed(A));
  cover property ($changed(B));
  cover property (@(posedge SUM or negedge SUM) 1'b1);
  cover property (@(posedge COUT or negedge COUT) 1'b1);

endmodule

// Bind into DUT
bind sky130_fd_sc_ms__ha sky130_fd_sc_ms__ha_sva i_ha_sva (.A(A), .B(B), .SUM(SUM), .COUT(COUT));

`endif