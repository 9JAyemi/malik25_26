// Bindable SVA for four_input_module
bind four_input_module four_input_module_sva sva();

module four_input_module_sva;

  // Power-good qualifier
  wire power_good = (VPWR === 1'b1) && (VGND === 1'b0);

  // Sample on any input/output transition
  default clocking cb @(
      posedge A1 or negedge A1 or
      posedge A2 or negedge A2 or
      posedge A3 or negedge A3 or
      posedge B1 or negedge B1 or
      posedge Y  or negedge Y
  ); endclocking

  default disable iff (!power_good);

  // Functional correctness when inputs are 2-state known
  assert property ( !$isunknown({A1,A2,A3,B1}) |-> (Y === (A1 | A2 | A3 | B1)) );

  // Priority chain forces
  assert property ( A1===1'b1                                              |-> Y===1'b1 );
  assert property ( A1===1'b0 && A2===1'b1                                 |-> Y===1'b1 );
  assert property ( A1===1'b0 && A2===1'b0 && A3===1'b1                    |-> Y===1'b1 );
  assert property ( A1===1'b0 && A2===1'b0 && A3===1'b0 && B1===1'b1       |-> Y===1'b1 );
  assert property ( A1===1'b0 && A2===1'b0 && A3===1'b0 && B1===1'b0       |-> Y===1'b0 );

  // No spurious Y change without an input change
  assert property ( $changed(Y) |-> $changed({A1,A2,A3,B1}) );

  // Insensitivity of lower-priority inputs
  assert property ( (A1===1'b1)                                         && $changed({A2,A3,B1}) |-> ##0 $stable(Y) );
  assert property ( (A1===1'b0 && A2===1'b1)                            && $changed({A3,B1})    |-> ##0 $stable(Y) );
  assert property ( (A1===1'b0 && A2===1'b0 && A3===1'b1)               && $changed(B1)         |-> ##0 $stable(Y) );

  // Basic functional coverage of each decision path and Y=0
  cover property ( power_good && A1===1'b1 );
  cover property ( power_good && A1===1'b0 && A2===1'b1 );
  cover property ( power_good && A1===1'b0 && A2===1'b0 && A3===1'b1 );
  cover property ( power_good && A1===1'b0 && A2===1'b0 && A3===1'b0 && B1===1'b1 );
  cover property ( power_good && A1===1'b0 && A2===1'b0 && A3===1'b0 && B1===1'b0 );

  // Y toggle coverage
  cover property ( power_good && $rose(Y) );
  cover property ( power_good && $fell(Y) );

endmodule