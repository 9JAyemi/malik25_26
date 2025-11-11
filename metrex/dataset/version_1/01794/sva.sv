// SVA checker for sky130_fd_sc_hdll__xnor3
module sky130_fd_sc_hdll__xnor3_sva (
  input logic A,
  input logic B,
  input logic C,
  input logic X
);

  // Sample on any input edge; use ##0 in properties to avoid preponed sampling races.
  default clocking cb @(posedge A or negedge A or
                        posedge B or negedge B or
                        posedge C or negedge C); endclocking

  // Functional equivalence (4-state exact): X must equal ~(A^B^C)
  property p_func_4state;
    1 |-> ##0 (X === ~(A ^ B ^ C));
  endproperty
  assert property (p_func_4state);

  // Known-input determinism: if inputs are 0/1, output is 0/1 and correct
  property p_known_inputs_det;
    !$isunknown({A,B,C}) |-> ##0 (!$isunknown(X) && X !== 1'bz && (X == ~(A ^ B ^ C)));
  endproperty
  assert property (p_known_inputs_det);

  // Output should never be Z (buf is not tri-state)
  property p_no_z_out;
    1 |-> ##0 (X !== 1'bz);
  endproperty
  assert property (p_no_z_out);

  // Basic toggle coverage on output
  cover property ($rose(X));
  cover property ($fell(X));

  // Truth-table coverage (inputs known) with expected X
  cover property ( (A==0 && B==0 && C==0) ##0 (X==1) );
  cover property ( (A==0 && B==0 && C==1) ##0 (X==0) );
  cover property ( (A==0 && B==1 && C==0) ##0 (X==0) );
  cover property ( (A==0 && B==1 && C==1) ##0 (X==1) );
  cover property ( (A==1 && B==0 && C==0) ##0 (X==0) );
  cover property ( (A==1 && B==0 && C==1) ##0 (X==1) );
  cover property ( (A==1 && B==1 && C==0) ##0 (X==1) );
  cover property ( (A==1 && B==1 && C==1) ##0 (X==0) );

  // X-propagation coverage: any unknown on inputs leads to unknown on output
  cover property ( $isunknown({A,B,C}) ##0 $isunknown(X) );

endmodule

// Bind the SVA to all instances of the DUT
bind sky130_fd_sc_hdll__xnor3 sky130_fd_sc_hdll__xnor3_sva sva_inst (.A(A), .B(B), .C(C), .X(X));