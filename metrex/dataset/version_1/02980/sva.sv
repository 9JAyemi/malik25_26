// SVA for sky130_fd_sc_hd__lpflow_inputiso1p
// X = A | SLEEP  (isolation: clamp-high when SLEEP=1, pass A when SLEEP=0)

module sky130_fd_sc_hd__lpflow_inputiso1p_sva (
  input logic A,
  input logic SLEEP,
  input logic X
);

  // Functional equivalence (4-state aware) and settle in same timestep
  property p_func; @(A or SLEEP or X) ##0 (X === (A | SLEEP)); endproperty
  assert property (p_func);

  // No X on output if inputs are known
  property p_no_x_when_inputs_known;
    @(A or SLEEP or X) (!$isunknown({A,SLEEP})) |-> ##0 (!$isunknown(X));
  endproperty
  assert property (p_no_x_when_inputs_known);

  // Output only changes when an input changes (no spontaneous glitches)
  property p_no_spurious_x;
    @(posedge X or negedge X) 1 |-> ($changed(A) || $changed(SLEEP));
  endproperty
  assert property (p_no_spurious_x);

  // Truth table coverage
  cover property (@(A or SLEEP) ##0 (A==0 && SLEEP==0 && X==0));
  cover property (@(A or SLEEP) ##0 (A==0 && SLEEP==1 && X==1));
  cover property (@(A or SLEEP) ##0 (A==1 && SLEEP==0 && X==1));
  cover property (@(A or SLEEP) ##0 (A==1 && SLEEP==1 && X==1));

  // Dynamic behavior coverage
  cover property (@(posedge A) (SLEEP==0) ##0 (X==1));  // pass-through rise
  cover property (@(negedge A) (SLEEP==0) ##0 (X==0));  // pass-through fall
  cover property (@(posedge A or negedge A) (SLEEP==1) ##0 (X==1)); // clamped
  cover property (@(posedge SLEEP) ##0 (X==1));          // enter isolation
  cover property (@(negedge SLEEP) ##0 (X===A));         // exit isolation
endmodule

bind sky130_fd_sc_hd__lpflow_inputiso1p sky130_fd_sc_hd__lpflow_inputiso1p_sva u_sva (.*);