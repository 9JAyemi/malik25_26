// SVA for sky130_fd_sc_ms__nand4bb
// Function: Y = A_N | B_N | ~(C & D)

bind sky130_fd_sc_ms__nand4bb sky130_fd_sc_ms__nand4bb_sva i_sva (.*);

module sky130_fd_sc_ms__nand4bb_sva (
  input Y, A_N, B_N, C, D,
  input nand0_out, or0_out_Y
);

  // Helper
  function automatic bit known_inputs;
    return !$isunknown({A_N,B_N,C,D});
  endfunction

  // Top-level functional equivalence (4-state, sampled after ##0)
  property p_func_eq;
    @(A_N or B_N or C or D or Y)
      ##0 known_inputs() |-> (Y === (A_N | B_N | ~(C & D)));
  endproperty
  assert property (p_func_eq);

  // Internal structure checks
  property p_nand0;
    @(C or D or nand0_out) ##0 !$isunknown({C,D}) |-> (nand0_out === ~(C & D));
  endproperty
  assert property (p_nand0);

  property p_or0;
    @(A_N or B_N or nand0_out or or0_out_Y)
      ##0 !$isunknown({A_N,B_N,nand0_out}) |-> (or0_out_Y === (B_N | A_N | nand0_out));
  endproperty
  assert property (p_or0);

  property p_buf0;
    @(or0_out_Y or Y) ##0 !$isunknown(or0_out_Y) |-> (Y === or0_out_Y);
  endproperty
  assert property (p_buf0);

  // Key implications
  property p_A_forces_high;
    @(A_N or Y) ##0 (known_inputs() && A_N) |-> (Y == 1'b1);
  endproperty
  assert property (p_A_forces_high);

  property p_B_forces_high;
    @(B_N or Y) ##0 (known_inputs() && B_N) |-> (Y == 1'b1);
  endproperty
  assert property (p_B_forces_high);

  property p_CorD_zero_forces_high;
    @(C or D or Y) ##0 (known_inputs() && ((C==0) || (D==0))) |-> (Y == 1'b1);
  endproperty
  assert property (p_CorD_zero_forces_high);

  property p_low_condition_only;
    @(A_N or B_N or C or D or Y)
      ##0 (known_inputs() && (Y==1'b0)) |-> (A_N==0 && B_N==0 && C==1 && D==1);
  endproperty
  assert property (p_low_condition_only);

  // X-prop: if inputs known, output must be known
  property p_no_x_on_Y_when_inputs_known;
    @(A_N or B_N or C or D or Y) ##0 known_inputs() |-> !$isunknown(Y);
  endproperty
  assert property (p_no_x_on_Y_when_inputs_known);

  // Coverage
  cover property (@(A_N or B_N or C or D or Y) ##0 (A_N==0 && B_N==0 && C==1 && D==1 && Y==0)); // sole low case
  cover property (@(A_N or B_N or C or D or Y) ##0 (A_N==1 && B_N==0 && C==1 && D==1 && Y==1)); // Y high due to A_N
  cover property (@(A_N or B_N or C or D or Y) ##0 (A_N==0 && B_N==1 && C==1 && D==1 && Y==1)); // Y high due to B_N
  cover property (@(A_N or B_N or C or D or Y) ##0 (A_N==0 && B_N==0 && C==0 && D==1 && Y==1)); // Y high due to ~C
  cover property (@(A_N or B_N or C or D or Y) ##0 (A_N==0 && B_N==0 && C==1 && D==0 && Y==1)); // Y high due to ~D
  cover property (@(Y) ##0 $rose(Y));
  cover property (@(Y) ##0 $fell(Y));

endmodule