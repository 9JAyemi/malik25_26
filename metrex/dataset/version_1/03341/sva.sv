// SVA checker for mux; bind to the DUT for verification-only use.
module mux_sva #(parameter N = 1)
(
  input        ctrl,
  input [N-1:0] D0,
  input [N-1:0] D1,
  input [N-1:0] S
);
  // synthesis translate_off

  // Functional equivalence holds after any driving signal changes (4-state accurate)
  property p_mux_equation;
    @(ctrl or D0 or D1 or S) ##0 (S === (ctrl ? D1 : D0));
  endproperty
  assert property (p_mux_equation)
    else $error("mux: S !== (ctrl ? D1 : D0)");

  // Cover both selections occur and produce the expected result
  cover property (@(posedge ctrl) ##0 (S === D1));
  cover property (@(negedge ctrl) ##0 (S === D0));

  // Cover data propagation when the selected input changes
  cover property (@(D1) (ctrl===1'b1) ##0 $changed(S));
  cover property (@(D0) (ctrl===1'b0) ##0 $changed(S));

  // Cover the degenerate case where inputs are equal (output independent of ctrl)
  cover property (@(ctrl or D0 or D1) (D0===D1) ##0 (S===D0));

  // synthesis translate_on
endmodule

// Example bind (place in a verification file)
// bind mux mux_sva #(.N(N)) mux_sva_i (.ctrl(ctrl), .D0(D0), .D1(D1), .S(S));