// SVA for sky130_fd_sc_ms__and3
// Bind this checker to the DUT to verify functionality and get coverage.

module sky130_fd_sc_ms__and3_sva;
  // Use any input/output edge as the sampling event
  default clocking cb @(posedge A or negedge A or
                        posedge B or negedge B or
                        posedge C or negedge C or
                        posedge X or negedge X);
  endclocking

  // Core functional equivalence (4-state correct)
  property p_and3_func;
    X === (A & B & C);
  endproperty
  assert property (p_and3_func) else $error("AND3 functional mismatch: X != A&B&C");

  // Buffer integrity (internal path equality)
  property p_buf_integrity;
    X === and0_out_X;
  endproperty
  assert property (p_buf_integrity) else $error("Buffer mismatch: X != and0_out_X");

  // No spurious X change without an input change
  property p_change_has_cause;
    $changed(X) |-> ($changed(A) or $changed(B) or $changed(C));
  endproperty
  assert property (p_change_has_cause) else $error("X changed without input change");

  // If all inputs are known, output must be known
  property p_known_out_when_known_in;
    (!$isunknown({A,B,C})) |-> (!$isunknown(X));
  endproperty
  assert property (p_known_out_when_known_in) else $error("X unknown while inputs known");

  // Functional coverage: all input combinations observed with correct X
  cover property (A===1'b0 && B===1'b0 && C===1'b0 && X===1'b0);
  cover property (A===1'b0 && B===1'b0 && C===1'b1 && X===1'b0);
  cover property (A===1'b0 && B===1'b1 && C===1'b0 && X===1'b0);
  cover property (A===1'b0 && B===1'b1 && C===1'b1 && X===1'b0);
  cover property (A===1'b1 && B===1'b0 && C===1'b0 && X===1'b0);
  cover property (A===1'b1 && B===1'b0 && C===1'b1 && X===1'b0);
  cover property (A===1'b1 && B===1'b1 && C===1'b0 && X===1'b0);
  cover property (A===1'b1 && B===1'b1 && C===1'b1 && X===1'b1);

  // Output edge coverage
  cover property ($rose(X));
  cover property ($fell(X));
endmodule

bind sky130_fd_sc_ms__and3 sky130_fd_sc_ms__and3_sva sva();