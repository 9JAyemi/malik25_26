// SVA for sky130_fd_sc_hdll__o21ai
// Bind-only; concise, functionally complete, with X-prop checks and full truth-table coverage.

module o21ai_sva (input logic Y, A1, A2, B1);

  function automatic bit known (logic v); return !$isunknown(v); endfunction

  // Sample on any input/output transition
  default clocking cb @(
      posedge A1 or negedge A1 or
      posedge A2 or negedge A2 or
      posedge B1 or negedge B1 or
      posedge Y  or negedge Y
  ); endclocking

  // 2-state functional correctness when inputs are known
  assert property ( (known(A1) && known(A2) && known(B1)) |-> (Y === ~(B1 & (A1 | A2))) )
    else $error("o21ai func mismatch: Y=%0b A1=%0b A2=%0b B1=%0b", Y,A1,A2,B1);

  // Dominance / simplifications (including X-safe cases)
  assert property ( B1 === 1'b0 |-> Y === 1'b1 );
  assert property ( (A1 === 1'b0) && (A2 === 1'b0) |-> Y === 1'b1 );
  assert property ( (A1 === 1'b1) && known(B1) |-> Y === ~B1 );
  assert property ( (A2 === 1'b1) && known(B1) |-> Y === ~B1 );

  // Expected X-propagation in ambiguous cases
  assert property ( (B1 === 1'b1) && (A1 === 1'b0) && $isunknown(A2) |-> $isunknown(Y) );
  assert property ( (B1 === 1'b1) && (A2 === 1'b0) && $isunknown(A1) |-> $isunknown(Y) );
  assert property ( $isunknown(B1) && ((A1 === 1'b1) || (A2 === 1'b1)) |-> $isunknown(Y) );

  // Functional coverage: all 8 input combinations with correct Y
  cover property ( known(A1)&&known(A2)&&known(B1) && (A1==0)&&(A2==0)&&(B1==0) && (Y===1) );
  cover property ( known(A1)&&known(A2)&&known(B1) && (A1==0)&&(A2==0)&&(B1==1) && (Y===1) );
  cover property ( known(A1)&&known(A2)&&known(B1) && (A1==0)&&(A2==1)&&(B1==0) && (Y===1) );
  cover property ( known(A1)&&known(A2)&&known(B1) && (A1==0)&&(A2==1)&&(B1==1) && (Y===0) );
  cover property ( known(A1)&&known(A2)&&known(B1) && (A1==1)&&(A2==0)&&(B1==0) && (Y===1) );
  cover property ( known(A1)&&known(A2)&&known(B1) && (A1==1)&&(A2==0)&&(B1==1) && (Y===0) );
  cover property ( known(A1)&&known(A2)&&known(B1) && (A1==1)&&(A2==1)&&(B1==0) && (Y===1) );
  cover property ( known(A1)&&known(A2)&&known(B1) && (A1==1)&&(A2==1)&&(B1==1) && (Y===0) );

  // Output toggle coverage
  cover property ( $rose(Y) );
  cover property ( $fell(Y) );

endmodule

bind sky130_fd_sc_hdll__o21ai o21ai_sva o21ai_sva_i (.*);